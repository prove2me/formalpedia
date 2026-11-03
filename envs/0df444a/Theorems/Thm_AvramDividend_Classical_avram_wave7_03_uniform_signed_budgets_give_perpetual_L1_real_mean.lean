-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_uniform_signed_budgets_give_perpetual_L1_real_mean
-- name    : AvramDividend.Classical.avram_wave7_03_uniform_signed_budgets_give_perpetual_L1_real_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:48:12.567446+00:00
-- url     : https://prove2.me/theorems/0376bd46-ee10-4bd0-88f2-f525d9102c1f
-- title:
--   Uniform genuine original signed Stieltjes budgets imply L1 full perpetual cash and exact real expected value
-- statement:
--   A short directly consumable original-process theorem for BV and UBV HJB proofs. If all original finite integer-horizon signed Stieltjes expectations on the exact canonical ruin-stopped paymentTimes∩Iic(n+1) and dividendMeasure Dω are at most a common real B, then the original perpetual dividend ENNReal fibre cash converted to real is P-integrable, and the canonical dividendValue equals ENNReal.ofReal of that complete genuine original real mean. The proof combines the Proved iff finiteness characterisation and Proved perpetual cash L1 real-mean identity, retaining time zero and continuous strictly pre-ruin payouts.
-- source:
--   Proved 000389d1-8b8e-45cf-b4d1-0a4e161b8c29 and 5f2772c6-96e6-4a7d-bab9-41e6750c07f1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_finite_iff_uniform_signed_horizon_mean_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_uniform_signed_budgets_give_perpetual_L1_real_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (B : ℝ)
    (hBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω : Ω,
          (∫⁻ t in paymentTimes (ruinTime X x D ω),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) := by sorry
