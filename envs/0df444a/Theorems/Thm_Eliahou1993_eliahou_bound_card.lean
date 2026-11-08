-- Prove2me | Theorems.Thm_Eliahou1993_eliahou_bound_card
-- name    : Eliahou1993.eliahou_bound_card
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T14:38:58.986143+00:00
-- url     : https://prove2.me/theorems/e75e1c9c-9327-4f33-bf47-dad5353e16b7
-- title:
--   Eliahou (1993) Theorem 1.1 (orbit cardinality bound): conditional bound $|\Omega| \ge 17{,}087{,}915$ for $\min \Omega > 2^{40}$
-- statement:
--   Let $c = (x_0, x_1, \dots, x_{L-1})$ be an injective cycle of length $L > 0$ of the compressed Collatz map $T$, so that its image $\Omega = \{x_0, x_1, \dots, x_{L-1}\}$ has cardinality $|\Omega| = L$. Conditional on the hypothesis that the minimum cycle element satisfies $\min \Omega > 2^{40}$, the orbit cardinality satisfies
--
--   $$
--   2^{40} < \min \Omega \implies |\Omega| \ge 17{,}087{,}915.
--   $$
--
--   This corollary translates the indexed cycle-length bound `Eliahou1993.eliahou_bound_of_min` directly into the orbit-set cardinality $\mathrm{Card}\, \Omega$ used in Eliahou (1993).
--
--   **Formalization Note** This bound is **conditional** on the explicit hypothesis `(2 : ℕ) ^ 40 < cyc.minElem` (and `Function.Injective cyc.seq`), which is passed as an explicit assumption and not certified on the platform. Stated in the `Eliahou1993` namespace (`Eliahou1993.eliahou_bound_card`). Adapted under the MIT License from `tangentproofs/eliahou-collatz-bounds` (commit `18cc351df2f942ddba4bf03feb9b75a70701497d`, Copyright (c) 2026 Michal Wallace; co-authored by Aristotle / Harmonic).
-- source:
--   Shalom Eliahou (1993), 'The 3x + 1 problem: new lower bounds on nontrivial cycle lengths', Discrete Mathematics 118(1-3), pp. 45–56, p. 46, Theorem 1.1; https://github.com/tangentproofs/eliahou-collatz-bounds/blob/18cc351df2f942ddba4bf03feb9b75a70701497d/Collatz/LinearForm.lean#L102-L107 (Adapted from tangentproofs/eliahou-collatz-bounds (commit 18cc351df2f942ddba4bf03feb9b75a70701497d, Copyright (c) 2026 Michal Wallace, MIT License; co-authored by Aristotle / Harmonic).)

/-
Adapted from https://github.com/tangentproofs/eliahou-collatz-bounds
(commit 18cc351df2f942ddba4bf03feb9b75a70701497d, file Collatz/LinearForm.lean),
formalizing:
  Shalom Eliahou (1993), "The 3x + 1 problem: new lower bounds on nontrivial
  cycle lengths", Discrete Mathematics 118(1-3), pp. 45–56, Theorem 1.1.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

MIT License — Copyright (c) 2026 Michal Wallace. See Definitions/Def_eliahou1993Cycle.lean for full notice.
-/
import Definitions.Def_eliahou1993Cycle

open Finset Eliahou1993

theorem Eliahou1993.eliahou_bound_card {L : ℕ} (cyc : CollatzCycle L)
    (hinj : Function.Injective cyc.seq)
    (hmin : (2 : ℕ) ^ 40 < cyc.minElem) :
    17087915 ≤ (Finset.univ.image cyc.seq).card := by sorry
