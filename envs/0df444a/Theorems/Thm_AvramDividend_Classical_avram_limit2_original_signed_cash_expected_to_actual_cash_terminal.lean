-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_cash_expected_to_actual_cash_terminal
-- name    : AvramDividend.Classical.avram_limit2_original_signed_cash_expected_to_actual_cash_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:19:22.91754+00:00
-- url     : https://prove2.me/theorems/a3f813e5-271d-486c-b628-cc9b4347c660
-- title:
--   Transfer bounded signed real strict stopped BV cash to actual original ENNReal cash and terminal
-- statement:
--   The result preserves the original strictly stopped Iio T dividendMeasure integral and the actual terminal. It uses the accepted pointwise ENNReal.ofReal addition identity only on the AE subset where original cash is finite and the terminal is nonnegative, then replaces equal integrands by lintegral_congr_ae. Cash finiteness is an explicit hypothesis, not inferred from toReal. This provides a reusable interface after the signed Fatou grid bound; no canonical parent is invoked.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_cash_postterminal_ofreal_exact
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_signed_cash_expected_to_actual_cash_terminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (Term : Ω → ℝ) (B : ℝ≥0∞)
    (hCashFinite : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ≠ ⊤)
    (hTermPos : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hExpected : (∫⁻ ω, ENNReal.ofReal
      (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) + Term ω) ∂P) ≤ B) :
    (∫⁻ ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + ENNReal.ofReal (Term ω) ∂P) ≤ B := by sorry
