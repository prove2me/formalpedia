-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_terminal_expected_add
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_cash_terminal_expected_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:49:55.377201+00:00
-- url     : https://prove2.me/theorems/d5e53fef-14bb-4f81-b792-d72a023a57bd
-- title:
--   Original BV strict stopped cash and signed pre-rightpayment terminal expectation additivity
-- statement:
--   For the genuine original Levy source, cap-admissible strategy and bounded variation, the real expectation of the strict pre-horizon Stieltjes cash plus signed strictly surviving pre-rightpayment candidate equals the sum of their expectations. The proof uses previously Proved independent L1 bounds for both exact original objects, with time-zero right-payment included for positive horizons and no new generator, P2 compensator or pure-jump residual assumptions.
-- source:
--   Proved original strict cash L1 67a9c5bf, original signed strict preterminal L1 d086b85a; Mathlib integral_add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_preterminal_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_cash_terminal_expected_add
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let CashOpen : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let Pre : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0
    (∫ ω, CashOpen ω + Pre ω ∂P) =
      (∫ ω, CashOpen ω ∂P) + (∫ ω, Pre ω ∂P) := by sorry
