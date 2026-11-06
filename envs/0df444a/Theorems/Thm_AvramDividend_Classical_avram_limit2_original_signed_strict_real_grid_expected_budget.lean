-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_strict_real_grid_expected_budget
-- name    : AvramDividend.Classical.avram_limit2_original_signed_strict_real_grid_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:22:48.539635+00:00
-- url     : https://prove2.me/theorems/6c88278f-d2f8-4e5c-be88-1c702cefba60
-- title:
--   Original signed strict stopped cash and real-grid expected Fatou budget
-- statement:
--   This helper consumes the exact signed pre-rightpayment stopped cash and terminal lower-liminf certificate required by the original BV c1e2f021 source, while using genuinely integrable, almost-everywhere nonnegative real grid payoffs. The accepted ofReal-integral bridge gives a uniform ENNReal grid mean bound and the accepted signed Fatou theorem gives the desired source expression expectation bound. It does not require false cash finiteness or nonnegative signed terminals and keeps the Iio horizon unchanged.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_strict_fatou_real_grid_certificate
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_signed_strict_real_grid_expected_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (Term : Ω → ℝ)
    (F : ℕ → Ω → ℝ) (B : ℝ)
    (hFmeas : ∀ n, Measurable (F n))
    (hFint : ∀ n, Integrable (F n) P)
    (hFpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hGridMean : ∀ n, (∫ ω, F n ω ∂P) ≤ B)
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
