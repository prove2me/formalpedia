-- Prove2me | Theorems.Thm_Eliahou1993_eliahou_bound_of_min
-- name    : Eliahou1993.eliahou_bound_of_min
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T14:38:58.880556+00:00
-- url     : https://prove2.me/theorems/2549b9de-83ba-46ea-a601-b3b75eb314dc
-- title:
--   Eliahou (1993) Theorem 1.1 (cycle length corollary): conditional bound $L \ge 17{,}087{,}915$ for $\min c > 2^{40}$
-- statement:
--   Let $c = (x_0, x_1, \dots, x_{L-1})$ be a positive cycle of length $L > 0$ of the compressed Collatz map $T$, and let $m = \min_{0 \le i < L} x_i$ be its minimum element. Conditional on the hypothesis that $m > 2^{40}$, the cycle length $L$ satisfies
--
--   $$
--   2^{40} < m \implies L \ge 17{,}087{,}915.
--   $$
--
--   This theorem combines the unconditional sandwich inequality with the continued-fraction analysis of $\log_2 3$ and automatically discharges the positivity of the odd-element count $k_1 > 0$.
--
--   **Formalization Note** This bound is **conditional** on the explicit hypothesis `(2 : ℕ) ^ 40 < cyc.minElem`, which is passed as an assumption of the theorem and is not certified on the platform. Stated in the `Eliahou1993` namespace (`Eliahou1993.eliahou_bound_of_min`). Adapted under the MIT License from `tangentproofs/eliahou-collatz-bounds` (commit `18cc351df2f942ddba4bf03feb9b75a70701497d`, Copyright (c) 2026 Michal Wallace; co-authored by Aristotle / Harmonic).
-- source:
--   Shalom Eliahou (1993), 'The 3x + 1 problem: new lower bounds on nontrivial cycle lengths', Discrete Mathematics 118(1-3), pp. 45–56, p. 46, Theorem 1.1; https://github.com/tangentproofs/eliahou-collatz-bounds/blob/18cc351df2f942ddba4bf03feb9b75a70701497d/Collatz/LinearForm.lean#L96-L99 (Adapted from tangentproofs/eliahou-collatz-bounds (commit 18cc351df2f942ddba4bf03feb9b75a70701497d, Copyright (c) 2026 Michal Wallace, MIT License; co-authored by Aristotle / Harmonic).)

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

open Eliahou1993

theorem Eliahou1993.eliahou_bound_of_min {L : ℕ} (cyc : CollatzCycle L)
    (hmin : (2 : ℕ) ^ 40 < cyc.minElem) :
    17087915 ≤ L := by sorry
