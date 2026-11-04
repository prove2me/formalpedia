-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_band_weight_uniform_positive
-- name    : AvramDividend.Classical.avram_p2_b_rate_negative_band_weight_uniform_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:40:45.473394+00:00
-- url     : https://prove2.me/theorems/60c95238-3b02-4630-b623-8116d474a3c1
-- title:
--   Uniform strictly positive fourth-exponential weight on separated negative Levy bands
-- statement:
--   For theta and epsilon strictly positive, and any negative mark y at most minus epsilon, the fourth power of exp(theta*y)-1 is bounded below by the explicit strictly positive constant (1-exp(-theta*epsilon))^4. This quantitatively permits division by the weight on negative bands when transporting finite weighted Lévy measures to compact negative-mark tests.

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_negative_band_weight_uniform_positive
    (θ ε y : ℝ) (hθ : 0 < θ) (hε : 0 < ε) (hy : y ≤ -ε) :
    0 < (1 - Real.exp (-(θ * ε))) ^ 4 ∧
      (1 - Real.exp (-(θ * ε))) ^ 4 ≤
        (Real.exp (θ * y) - 1) ^ 4  := by sorry
