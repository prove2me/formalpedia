-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_expected_to_true_strict_cash_without_extra_finiteness
-- name    : AvramDividend.Classical.avram_limit2_original_signed_expected_to_true_strict_cash_without_extra_finiteness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:51:21.772437+00:00
-- url     : https://prove2.me/theorems/dfb5eb68-3ae4-48ce-bd59-8ee7bb08d14e
-- title:
--   Original signed finite stopped cash mean controls genuine ENNReal payoff without extra cash finiteness
-- statement:
--   The admitted source-specific stopped payment Stieltjes upper bound gives pathwise finiteness on each nonnegative finite T without any survival assumption. Therefore original Cash.toReal is exact. Combine that lemma with the accepted expected signed-real to actual ENNReal cash-plus-nonnegative-terminal transfer. Required assumptions are genuine IsDividendStrategy D, q>=0, T>=0 and AE nonnegative real prepayment terminal. This closes the finiteness interface of the P3 signed Fatou grid without assuming terminal vanishing, equality-in-law or altering strict Iio horizon.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_discounted_cash_finite_all_paths
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_cash_expected_to_actual_cash_terminal
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_signed_expected_to_true_strict_cash_without_extra_finiteness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 ≤ T) (Term : Ω → ℝ) (B : ℝ≥0∞)
    (hTermPos : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hExpected : (∫⁻ ω, ENNReal.ofReal
      (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) + Term ω) ∂P) ≤ B) :
    (∫⁻ ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + ENNReal.ofReal (Term ω) ∂P) ≤ B := by sorry
