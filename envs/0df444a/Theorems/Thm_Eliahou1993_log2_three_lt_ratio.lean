-- Prove2me | Theorems.Thm_Eliahou1993_log2_three_lt_ratio
-- name    : Eliahou1993.log2_three_lt_ratio
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T14:38:56.642359+00:00
-- url     : https://prove2.me/theorems/2610b12c-77ca-4e1c-b142-78fd3e547497
-- title:
--   Eliahou (1993) Theorem 2.1 corollary: strict lower bound $\log_2 3 < L / k_1$
-- statement:
--   Let $c = (x_0, x_1, \dots, x_{L-1})$ be a positive cycle of length $L > 0$ of the compressed Collatz map $T$ with $k_1 > 0$ odd elements. Then the ratio of total cycle length to odd elements satisfies the strict inequality
--
--   $$
--   \log_2 3 < \frac{L}{k_1}.
--   $$
--
--   This unconditional lower bound holds for every positive compressed Collatz cycle and supplies the left endpoint of the half-open interval $(\log_2 3, \log_2(3 + 1/m)]$ used in continued-fraction approximations.
--
--   **Formalization Note** Stated in the `Eliahou1993` namespace (`Eliahou1993.log2_three_lt_ratio`). Adapted under the MIT License from `tangentproofs/eliahou-collatz-bounds` (commit `18cc351df2f942ddba4bf03feb9b75a70701497d`, Copyright (c) 2026 Michal Wallace; co-authored by Aristotle / Harmonic).
-- source:
--   Shalom Eliahou (1993), 'The 3x + 1 problem: new lower bounds on nontrivial cycle lengths', Discrete Mathematics 118(1-3), pp. 45–56, p. 48, Theorem 2.1; https://github.com/tangentproofs/eliahou-collatz-bounds/blob/18cc351df2f942ddba4bf03feb9b75a70701497d/Collatz/Sandwich.lean#L114-L121 (Adapted from tangentproofs/eliahou-collatz-bounds (commit 18cc351df2f942ddba4bf03feb9b75a70701497d, Copyright (c) 2026 Michal Wallace, MIT License; co-authored by Aristotle / Harmonic).)

/-
Adapted from https://github.com/tangentproofs/eliahou-collatz-bounds
(commit 18cc351df2f942ddba4bf03feb9b75a70701497d, file Collatz/Sandwich.lean),
formalizing:
  Shalom Eliahou (1993), "The 3x + 1 problem: new lower bounds on nontrivial
  cycle lengths", Discrete Mathematics 118(1-3), pp. 45–56, Theorem 2.1.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

MIT License — Copyright (c) 2026 Michal Wallace. See Definitions/Def_eliahou1993Cycle.lean for full notice.
-/
import Definitions.Def_eliahou1993Cycle
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Finset BigOperators Real Eliahou1993

theorem Eliahou1993.log2_three_lt_ratio {L : ℕ} (c : CollatzCycle L) (hk : 0 < c.numOdd) :
    Real.logb 2 3 < (L : ℝ) / c.numOdd := by sorry
