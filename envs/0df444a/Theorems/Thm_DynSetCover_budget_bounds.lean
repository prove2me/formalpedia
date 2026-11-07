-- Prove2me | Theorems.Thm_DynSetCover_budget_bounds
-- name    : DynSetCover.budget_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:46:10.242725+00:00
-- url     : https://prove2.me/theorems/fe1052b5-a5ba-44b5-9d7f-abf938dca5cf
-- title:
--   §5 — at most $2048$ openings, commits and deletions and $2048L$ movements per update
-- statement:
--   Throughout, the states and update boundaries are those of admissible runs of the faster algorithm of §5 with capacity $N\ge2$ on valid update sequences keeping $|A_t|\le N$, with $L=\lceil\log_2(2N)\rceil$ and $\eta=1/L$.
--
--   Let an input update be processed from an update boundary, and let $o_1,\dots,o_k$ be operations executed in its repair phase (with the fresh budget of $2048$ points). Then
--   1. at most $2048$ of them are openings, commits or deletions;
--   2. at most $2048\,L$ of them are element movements (decrement continuations, starting increments, increment continuations);
--   3. the copy additions and deletions, namely the openings, the deletions and, for an arrival, the fresh copy, number at most $2049$;
--   4. consequently the physical cover changes by at most $2049$ input sets.
--
--   Thus each update performs $O(1)$ copy changes and $O(L)=O(\log N)$ element movements, which is what bounds the recourse and, in §7, the update time.
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - generalization: the run of the §5 algorithm with FIFO tie-breaking inside each priority and category, continuations moving the head element of a list, and one fixed cheapest set $S_e$ per element → every admissible run: any operation that is applicable and maximal in (priority, category order), any element of the list, and any choice of cheapest sets; reason: no proof in §§5–6 uses the FIFO or head-element rules or the particular cheapest set; the paper's run is one admissible run
--   - generalization: the operations performed by one input update → every sequence of operations executed in the update's repair phase, complete or not; reason: a prefix of the phase executes fewer operations, so the bounds for the complete phase are the case of a stopped phase
--   - generalization: $O(1)$ copy additions and deletions per update → also: the symmetric difference of the physical covers before the update and after the operations has at most $2049$ sets; reason: an added conclusion: adding or deleting a copy changes the physical cover by at most one set (p.15), and no other operation changes the retained copies
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), §5, Scheduling and work budget, p.41 (PDF 43)

import Mathlib
import Definitions.Def_DynSetCover_Algorithm

namespace DynSetCover

/-- **§5 "Scheduling and work budget"** (Paul, Solomon, STOC 2027 submission, sha256
a671756b…, p.41 (PDF 43)). "The budget permits at most 2048 openings, commits, and empty-copy
deletions in total, and at most 2048L individual element movements. Hence each input update
performs O(1) copy additions and deletions and O(L) = O(log N) element movements. Adding the
fresh copy for an arriving element occurs before these scheduled operations and contributes at
most one additional copy addition."

For every input update processed from an update boundary, and every sequence `ops` of
operations executed in its repair phase: at most `2048` are openings, commits or deletions; at
most `2048·L` are element movements; the copy additions and deletions, including the fresh copy
of an arrival, number at most `2049`; and hence the physical cover changes by at most `2049`
sets.

**Formalization Note.** The last clause (symmetric difference of the physical covers before the
update and at the end of the phase) is the recourse consequence of "Adding or deleting a copy
changes the physical cover by at most one set" (p.15); it is an added conclusion. -/
theorem budget_bounds (inst : Instance) (N : ℕ) (hN : 2 ≤ N) (ce : Fin inst.u → Fin inst.m)
    (hce : inst.IsCheapest ce) (s : State inst) (hs : IsBoundary inst N ce s)
    (x : Upd inst.u) (hx : UpdateOK inst N s x) (ops : List (Op inst)) (s' : State inst)
    (b' : ℝ) (hp : Phase inst N (applyUpdate inst ce s x) 2048 ops s' b') :
    ops.countP Op.isHeavy ≤ 2048 ∧
    ops.countP Op.isMove ≤ 2048 * capL N ∧
    ops.countP Op.changesCopies + (if x.isIns then 1 else 0) ≤ 2049 ∧
    ((physCover inst s' \ physCover inst s) ∪ (physCover inst s \ physCover inst s')).card ≤ 2049 := by sorry

end DynSetCover
