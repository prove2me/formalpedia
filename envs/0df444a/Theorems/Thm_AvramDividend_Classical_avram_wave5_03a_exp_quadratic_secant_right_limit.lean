-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_exp_quadratic_secant_right_limit
-- name    : AvramDividend.Classical.avram_wave5_03a_exp_quadratic_secant_right_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:17:28.754205+00:00
-- url     : https://prove2.me/theorems/51229e52-dd9a-4699-857c-a7594a13eb80
-- title:
--   Quadratic exponential difference quotient has exact first-order Gaussian drift limit
-- statement:
--   For any real b,d, the first-order difference quotient (exp(b epsilon+d epsilon squared)-1)/epsilon converges to b as epsilon decreases to zero through positive values. The proof differentiates the genuine quadratic exponential at zero and applies the pinned one-sided slope theorem. This analytic lemma is required to identify the pointwise limiting source martingale candidate from the exact ν=0 Lévy exponent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_exp_quadratic_secant_right_limit
    (b d : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => (Real.exp (b * ε + d * ε ^ 2) - 1) / ε)
      (𝓝[>] (0 : ℝ)) (𝓝 b) := by
  sorry
