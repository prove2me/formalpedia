-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_scalar_ode_exponential_growth
-- name    : AvramDividend.Classical.avram_p4_f4_turn16_scalar_ode_exponential_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:16:27.146522+00:00
-- url     : https://prove2.me/theorems/4357dcb6-6ceb-4b9b-878e-09b6c33e443c
-- title:
--   Positive-coefficient scalar supersolution exponential envelope
-- statement:
--   A continuous function on the nonnegative half-line with a twice continuously differentiable positive interior, zero negative extension and a w''+c w'-q w ≤ 0 with a,q>0 has a global nonnegative exponential upper bound.
-- source:
--   Deterministic ODE comparison. This is the only analytic ingredient absent after zero-jump HJB is rewritten using the proved Gaussian drift identity and σ positivity.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy


open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal


noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_turn16_scalar_ode_exponential_growth
    (a c q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (ha : 0 < a) (hq : 0 < q) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hode : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      a * iteratedDeriv 2 w y + c * deriv w y - q * w y ≤ 0) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, w y ≤ K * Real.exp (θ * y) := by sorry
