-- Prove2me | Theorems.Thm_Eliahou1993_eliahou_sandwich
-- name    : Eliahou1993.eliahou_sandwich
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T14:38:54.579866+00:00
-- url     : https://prove2.me/theorems/d682291c-4e32-4920-9383-9d24b2b76a28
-- title:
--   Eliahou (1993) Theorem 2.1: logarithmic sandwich inequality for Collatz cycles
-- statement:
--   Let $c = (x_0, x_1, \dots, x_{L-1})$ be a cycle of length $L > 0$ of the compressed Collatz map $T$ with $k_1 > 0$ odd elements, minimum element $m = \min_i x_i$, and maximum element $M = \max_i x_i$. Then the ratio $L / k_1$ is bounded above and below by
--
--   $$
--   \log_2\!\left(3 + \frac{1}{M}\right) \le \frac{L}{k_1} \le \log_2\!\left(3 + \frac{1}{m}\right).
--   $$
--
--   This unconditional sandwich inequality (Eliahou 1993, Theorem 2.1) is completely parametric in the cycle's minimum $m$ and maximum $M$ (requiring no $2^{40}$ hypothesis), and constrains $L / k_1$ to an interval of width at most $\log_2(3 + 1/m) - \log_2 3 < 1 / (3 m \ln 2)$.
--
--   **Formalization Note** Stated in the `Eliahou1993` namespace (`Eliahou1993.eliahou_sandwich`). Adapted under the MIT License from `tangentproofs/eliahou-collatz-bounds` (commit `18cc351df2f942ddba4bf03feb9b75a70701497d`, Copyright (c) 2026 Michal Wallace; co-authored by Aristotle / Harmonic).
-- source:
--   Shalom Eliahou (1993), 'The 3x + 1 problem: new lower bounds on nontrivial cycle lengths', Discrete Mathematics 118(1-3), pp. 45–56, p. 48, Theorem 2.1; https://github.com/tangentproofs/eliahou-collatz-bounds/blob/18cc351df2f942ddba4bf03feb9b75a70701497d/Collatz/Sandwich.lean#L106-L109 (Adapted from tangentproofs/eliahou-collatz-bounds (commit 18cc351df2f942ddba4bf03feb9b75a70701497d, Copyright (c) 2026 Michal Wallace, MIT License; co-authored by Aristotle / Harmonic).)

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

theorem Eliahou1993.eliahou_sandwich {L : ℕ} (c : CollatzCycle L) (hk : 0 < c.numOdd) :
    Real.logb 2 (3 + 1 / (c.maxElem : ℝ)) ≤ (L : ℝ) / c.numOdd ∧
    (L : ℝ) / c.numOdd ≤ Real.logb 2 (3 + 1 / (c.minElem : ℝ)) := by sorry
