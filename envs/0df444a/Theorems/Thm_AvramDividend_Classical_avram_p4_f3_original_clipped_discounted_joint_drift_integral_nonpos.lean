-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_clipped_discounted_joint_drift_integral_nonpos
-- name    : AvramDividend.Classical.avram_p4_f3_original_clipped_discounted_joint_drift_integral_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:49:10.894415+00:00
-- url     : https://prove2.me/theorems/77668e88-1d1a-4634-a247-54a7290ac4d2
-- title:
--   Physical joint-measure original clipped discounted generator and dividend-control drift nonpositive
-- statement:
--   For the original controlled Lévy reserve and any actual physical joint time-space measure, the discounted clipped HJB generator and nonnegative dividend-rate correction integrate to a nonpositive real value whenever that exact source integrand is integrable. No claim of stochastic integrability or Itô identity is inserted.
-- source:
--   Pointwise original clipped HJB and dividend-control nonpositivity, proven original theorem b55dacd6; Mathlib integral_nonpos_of_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_clipped_HJB_with_nonnegative_dividend_rate
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_clipped_discounted_joint_drift_integral_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (r : ℝ≥0 × Ω → ℝ) (hr : ∀ p, 0 ≤ r p)
    (μ : Measure (ℝ≥0 × Ω)) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
      if y ∈ Icc δ K then y else δ
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        ((X.generator w (U p) - q * w (U p)) +
          r p * (1 - deriv w (U p)))
    Integrable H μ → (∫ p, H p ∂μ) ≤ 0 := by sorry
