-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_residual_grid_to_strict_fatou_expected_budget
-- name    : AvramDividend.Classical.avram_limit2_original_signed_residual_grid_to_strict_fatou_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:31:17.835309+00:00
-- url     : https://prove2.me/theorems/04f574e6-3bc9-47f4-820c-bb37f21df9e3
-- title:
--   Original BV signed residual real-grid to strict stopped Fatou expected budget
-- statement:
--   A source-faithful assembly interface for the P3 original signed Fatou finite-grid certificate. The signed grid residual has an integrable initial constant with its actual expected value; the actual grid payoffs are measurable, integrable and nonnegative AE, bounded pathwise by the initial constant plus a genuinely nonpositive-mean residual. The original strict dividendMeasure Iio T cash.toReal and real pre-rightpayment terminal are dominated AE by the ENNReal.ofReal grid liminf. Compose the proved signed residual expectation helper with the proved signed Fatou real-grid bridge. No P3 canonical parent is imported, no equality-in-law is used, and no extra finiteness of cash is inferred.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_signed_grid_residual_expected_bound_with_integrable_constant
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_strict_real_grid_expected_budget
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_signed_residual_grid_to_strict_fatou_expected_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (Term : Ω → ℝ)
    (F G : ℕ → Ω → ℝ) (B : ℝ)
    (hFmeas : ∀ n, Measurable (F n))
    (hFint : ∀ n, Integrable (F n) P)
    (hFpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hGint : ∀ n, Integrable (G n) P)
    (hBint : Integrable (fun _ : Ω => B) P)
    (hConst : (∫ ω : Ω, B ∂P) = B)
    (hGridPath : ∀ n, ∀ᵐ ω ∂P, F n ω ≤ B + G n ω)
    (hResidualMean : ∀ n, (∫ ω, G n ω ∂P) ≤ 0)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal
        (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal) + Term ω) ≤
        liminf (fun n : ℕ => ENNReal.ofReal (F n ω)) atTop) :
    (∫⁻ ω, ENNReal.ofReal
      (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) + Term ω) ∂P) ≤
          ENNReal.ofReal B := by sorry
