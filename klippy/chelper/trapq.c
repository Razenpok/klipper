// Trapezoidal velocity movement queue
//
// Copyright (C) 2018-2021  Kevin O'Connor <kevin@koconnor.net>
//
// This file may be distributed under the terms of the GNU GPLv3 license.

#include <math.h> // sqrt
#include <stddef.h> // offsetof
#include <stdlib.h> // malloc
#include <string.h> // memset
#include "compiler.h" // unlikely
#include "trapq.h" // move_get_coord

/****************************************************************
 * ulist - Unrolled double linked lists
 * moves are often iterated, and we want to be cache friendly
 ****************************************************************/

static inline void
ulist_pod_init(struct ulist_pod *h)
{
    h->prev = h->next = h;
}

static inline int
ulist_empty(const struct ulist_pod *h)
{
    if (h->next != h)
        return 0;
    for (int i = 0; i < ULIST_ARRAY_SIZE; i++) {
        if (h->items[i].node.is_used)
            return 0;
    }
    return 1;
}

static inline void
ulist_del(struct move *m)
{
    const struct move *fm = m - m->node.index;
    const struct ulist_pod *cpod = (struct ulist_pod *)fm;
    struct ulist_pod *prev = cpod->prev;
    struct ulist_pod *next = cpod->next;
    m->node.is_used = 0;
    // check pod is empty
    for (int i = 0; i < ULIST_ARRAY_SIZE; i++) {
        if (cpod->items[i].node.is_used) {
            return;
        }
    }

    // We are first one - static
    if (prev == cpod) {
        return;
    }
    // we are last one
    if (next == cpod) {
        prev->next = prev;
        free((void *)cpod);
        return;
    }
    prev->next = next;
    next->prev = prev;
    free((void *)cpod);
}

struct move *
ulist_first_entry(struct ulist_pod *h)
{
    while (1) {
        for (int i = 0; i < ULIST_ARRAY_SIZE; i++) {
            if (h->items[i].node.is_used) {
                return &h->items[i];
            }
        }
        if (h->next == h)
            break;
        h = h->next;
    }
}

struct move *
ulist_last_entry(struct ulist_pod *h)
{
    struct move *last;
    while(1) {
        for (int i = 0; i < ULIST_ARRAY_SIZE; i++) {
            if (h->items[i].node.is_used) {
                last = &h->items[i];
            }
        }
        if (h->next == h)
            break;
        h = h->next;
    };

    return last;
}

struct move *
ulist_prev_entry(struct move *m)
{
    const struct move *fm = m - m->node.index;
    struct ulist_pod *cpod = (struct ulist_pod *)fm;
    while (1) {
        for (int i = m->node.index - 1; i >= 0; i--) {
            if (cpod->items[i].node.is_used) {
                return &cpod->items[i];
            }
        }
        if (cpod == cpod->prev)
            break;
        cpod = cpod->prev;
    }
}

struct move *
ulist_next_entry(struct move *m)
{
    const struct move *fm = m - m->node.index;
    struct ulist_pod *cpod = (struct ulist_pod *)fm;
    for (int i = m->node.index + 1; i < ULIST_ARRAY_SIZE; i++) {
        if (cpod->items[i].node.is_used) {
            return &cpod->items[i];
        }
    }
    cpod = cpod->next;
    while (1) {
        for (int i = 0; i < ULIST_ARRAY_SIZE; i++) {
            if (cpod->items[i].node.is_used) {
                return &cpod->items[i];
            }
        }
        if (cpod->next == cpod)
            break;
        cpod = cpod->next;
    }
}

// handles only insertion before last item
static inline void
ulist_add_before(struct move *m, struct move *next_move)
{
    const struct move *fm = next_move - next_move->node.index;
    struct ulist_pod *cpod = (struct ulist_pod *)fm;
    int cindex = next_move->node.index;
    if (cindex > 0 && !cpod->items[cindex - 1].node.is_used) {
        cpod->items[cindex - 1] = *m;
        cpod->items[cindex - 1].node.index = cindex - 1;
        cpod->items[cindex - 1].node.is_used = 1;
        return;
    }
    // shift values by one right if empty
    if (cindex + 1 < ULIST_ARRAY_SIZE && !cpod->items[cindex + 1].node.is_used) {
        cpod->items[cindex + 1] = cpod->items[cindex];
        cpod->items[cindex + 1].node.index = cindex + 1;
        cpod->items[cindex] = *m;
        cpod->items[cindex].node.is_used = 1;
        cpod->items[cindex].node.index = cindex;
        return;
    }
    // if last -> add new pod
    if (cindex + 1 == ULIST_ARRAY_SIZE) {
        if (cpod->next == cpod) {
            struct ulist_pod *new_pod = (struct ulist_pod *)malloc(sizeof(*new_pod));
            cpod->next = new_pod;
            new_pod->next = new_pod;
            new_pod->prev = cpod;
            new_pod->items[0] = cpod->items[cindex];
            new_pod->items[0].node.index = 0;
            cpod->items[cindex] = *m;
            cpod->items[cindex].node.is_used = 1;
            cpod->items[cindex].node.index = cindex;
            return;
        }
    }
}


static inline void
ulist_add_head(struct move *m, struct ulist_pod *h)
{
    if (!h->items[0].node.is_used) {
        h->items[0] = *m;
        h->items[0].node.is_used = 1;
        h->items[0].node.index = 0;
        return;
    }
    int next_empty = -1;
    for (int i = 0; i < ULIST_ARRAY_SIZE; i++) {
        if (!h->items[i].node.is_used) {
            next_empty = i;
            break;
        }
    }
    if (next_empty > 0) {
        for (int i = next_empty; i > 0; i--) {
            h->items[i] = h->items[i-1];
            h->items[i].node.index = i;
        }
        h->items[0] = *m;
        h->items[0].node.is_used = 1;
        h->items[0].node.index = 0;
        return;
    }
    // split
    struct ulist_pod *new_pod = (struct ulist_pod *)malloc(sizeof(*new_pod));
    struct ulist_pod *old_next = h->next;
    h->next = new_pod;
    new_pod->prev = h;
    if (old_next != h) {
        new_pod->next = old_next;
        old_next->prev = new_pod;
    } else {
        new_pod->next = new_pod;
    }
    for (int i = 0; i < ULIST_ARRAY_SIZE; i++) {
        memcpy(&new_pod->items[i], &h->items[i], sizeof(*m));
        memset(&h->items[i], 0, sizeof(*m));
    }
    if (!h->items[0].node.is_used) {
        h->items[0] = *m;
        h->items[0].node.is_used = 1;
        h->items[0].node.index = 0;
        return;
    }
}

// Return the distance moved given a time in a move
inline double
move_get_distance(struct move *m, double move_time)
{
    return (m->start_v + m->half_accel * move_time) * move_time;
}

// Return the XYZ coordinates given a time in a move
inline struct coord
move_get_coord(struct move *m, double move_time)
{
    double move_dist = move_get_distance(m, move_time);
    return (struct coord) {
        .x = m->start_pos.x + m->axes_r.x * move_dist,
        .y = m->start_pos.y + m->axes_r.y * move_dist,
        .z = m->start_pos.z + m->axes_r.z * move_dist };
}

#define NEVER_TIME 9999999999999999.9

// Allocate a new 'trapq' object
struct trapq * __visible
trapq_alloc(void)
{
    struct trapq *tq = (struct trapq *)malloc(sizeof(*tq));
    memset(tq, 0, sizeof(*tq));
    ulist_pod_init(&tq->moves);
    ulist_pod_init(&tq->history);
    // head sentinel
    tq->moves.items[0].node.is_used = 1;
    tq->moves.items[0].node.index = 0;
    // tail sentinel
    tq->moves.items[1].node.is_used = 1;
    tq->moves.items[1].node.index = 1;
    tq->moves.items[1].print_time = NEVER_TIME;
    tq->moves.items[1].move_t = NEVER_TIME;
    return tq;
}

// Free memory associated with a 'trapq' object
void __visible
trapq_free(struct trapq *tq)
{
    while (!ulist_empty(&tq->moves)) {
        struct move *m = ulist_first_entry(&tq->moves);
        ulist_del(m);
    }
    while (!ulist_empty(&tq->history)) {
        struct move *m = ulist_first_entry(&tq->history);
        ulist_del(m);
    }
    free(tq);
}

// Update the list sentinels
void
trapq_check_sentinels(struct trapq *tq)
{
    struct move *tail_sentinel = ulist_last_entry(&tq->moves);
    if (tail_sentinel->print_time)
        // Already up to date
        return;
    struct move *m = ulist_prev_entry(tail_sentinel);
    struct move *head_sentinel = ulist_first_entry(&tq->moves);
    if (m == head_sentinel) {
        // No moves at all on this list
        tail_sentinel->print_time = NEVER_TIME;
        return;
    }
    tail_sentinel->print_time = m->print_time + m->move_t;
    tail_sentinel->start_pos = move_get_coord(m, m->move_t);
}

#define MAX_NULL_MOVE 1.0

// Add a move to the trapezoid velocity queue
void
trapq_add_move(struct trapq *tq, struct move *m)
{
    struct move *tail_sentinel = ulist_last_entry(&tq->moves);
    struct move *prev = ulist_prev_entry(tail_sentinel);
    if (prev->print_time + prev->move_t < m->print_time) {
        // Add a null move to fill time gap
        struct move null_move;
        null_move.start_pos = m->start_pos;
        if (!prev->print_time && m->print_time > MAX_NULL_MOVE)
            // Limit the first null move to improve numerical stability
            null_move.print_time = m->print_time - MAX_NULL_MOVE;
        else
            null_move.print_time = prev->print_time + prev->move_t;
        null_move.move_t = m->print_time - null_move.print_time;
        ulist_add_before(&null_move, tail_sentinel);
    }
    ulist_add_before(m, tail_sentinel);
    tail_sentinel->print_time = 0.;
}

// Fill and add a move to the trapezoid velocity queue
void __visible
trapq_append(struct trapq *tq, double print_time
             , double accel_t, double cruise_t, double decel_t
             , double start_pos_x, double start_pos_y, double start_pos_z
             , double axes_r_x, double axes_r_y, double axes_r_z
             , double start_v, double cruise_v, double accel)
{
    struct coord start_pos = { .x=start_pos_x, .y=start_pos_y, .z=start_pos_z };
    struct coord axes_r = { .x=axes_r_x, .y=axes_r_y, .z=axes_r_z };
    if (accel_t) {
        struct move m;
        memset(&m, 0, sizeof(m));
        m.print_time = print_time;
        m.move_t = accel_t;
        m.start_v = start_v;
        m.half_accel = .5 * accel;
        m.start_pos = start_pos;
        m.axes_r = axes_r;
        trapq_add_move(tq, &m);

        print_time += accel_t;
        start_pos = move_get_coord(&m, accel_t);
    }
    if (cruise_t) {
        struct move m;
        memset(&m, 0, sizeof(m));
        m.print_time = print_time;
        m.move_t = cruise_t;
        m.start_v = cruise_v;
        m.half_accel = 0.;
        m.start_pos = start_pos;
        m.axes_r = axes_r;
        trapq_add_move(tq, &m);

        print_time += cruise_t;
        start_pos = move_get_coord(&m, cruise_t);
    }
    if (decel_t) {
        struct move m;
        memset(&m, 0, sizeof(m));
        m.print_time = print_time;
        m.move_t = decel_t;
        m.start_v = cruise_v;
        m.half_accel = -.5 * accel;
        m.start_pos = start_pos;
        m.axes_r = axes_r;
        trapq_add_move(tq, &m);
    }
}

// Expire any moves older than `print_time` from the trapezoid velocity queue
void __visible
trapq_finalize_moves(struct trapq *tq, double print_time
                     , double clear_history_time)
{
    struct move *head_sentinel = ulist_first_entry(&tq->moves);
    struct move *tail_sentinel = ulist_last_entry(&tq->moves);
    // Move expired moves from main "moves" list to "history" list
    for (;;) {
        struct move *m = ulist_next_entry(head_sentinel);
        if (m == tail_sentinel) {
            tail_sentinel->print_time = NEVER_TIME;
            break;
        }
        if (m->print_time + m->move_t > print_time)
            break;
        // copy memory before delete
        if (m->start_v || m->half_accel)
            ulist_add_head(m, &tq->history);
        ulist_del(m);
    }
    // Free old moves from history list
    if (ulist_empty(&tq->history))
        return;
    struct move *latest = ulist_first_entry(&tq->history);
    for (;;) {
        struct move *m = ulist_last_entry(&tq->history);
        if (m == latest || m->print_time + m->move_t > clear_history_time)
            break;
        ulist_del(m);
    }
}

// Note a position change in the trapq history
void __visible
trapq_set_position(struct trapq *tq, double print_time
                   , double pos_x, double pos_y, double pos_z)
{
    // Flush all moves from trapq
    trapq_finalize_moves(tq, NEVER_TIME, 0);

    // Prune any moves in the trapq history that were interrupted
    while (!ulist_empty(&tq->history)) {
        struct move *m = ulist_first_entry(&tq->history);
        if (m->print_time < print_time) {
            if (m->print_time + m->move_t > print_time)
                m->move_t = print_time - m->print_time;
            break;
        }
        ulist_del(m);
    }

    // Add a marker to the trapq history
    struct move m;
    memset(&m, 0, sizeof(m));
    m.print_time = print_time;
    m.start_pos.x = pos_x;
    m.start_pos.y = pos_y;
    m.start_pos.z = pos_z;
    ulist_add_head(&m, &tq->history);
}

// Return history of movement queue
int __visible
trapq_extract_old(struct trapq *tq, struct pull_move *p, int max
                  , double start_time, double end_time)
{
    int res = 0;
    struct move *m;
    struct move *last = ulist_last_entry(&tq->history);
    for (m = ulist_first_entry(&tq->history); m != last; m = ulist_next_entry(m)) {
        if (start_time >= m->print_time + m->move_t || res >= max)
            break;
        if (end_time <= m->print_time)
            continue;
        p->print_time = m->print_time;
        p->move_t = m->move_t;
        p->start_v = m->start_v;
        p->accel = 2. * m->half_accel;
        p->start_x = m->start_pos.x;
        p->start_y = m->start_pos.y;
        p->start_z = m->start_pos.z;
        p->x_r = m->axes_r.x;
        p->y_r = m->axes_r.y;
        p->z_r = m->axes_r.z;
        p++;
        res++;
    }
    return res;
}
