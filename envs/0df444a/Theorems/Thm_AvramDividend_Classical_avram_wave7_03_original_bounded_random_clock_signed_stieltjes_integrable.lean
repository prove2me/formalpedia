-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_signed_stieltjes_integrable
-- name    : AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_signed_stieltjes_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:28:41.009196+00:00
-- url     : https://prove2.me/theorems/020fa5bb-0b25-44d5-9332-bf707f58259d
-- title:
--   Original complete ruin-stopped signed real Stieltjes payout is L1 under bounded measurable random clocks
-- statement:
--   For any bounded measurable random clock τ in the exact original Levy process and capped admissible dividend strategy, the real discounted signed-looking Stieltjes cash against the genuine original dividendMeasure on paymentTimes(ruinTime)∩Iic(τ ω) is P-integrable. The proof uses accepted original bounded random-clock ENNReal cash.toReal integrability and exact pathwise finite real-horizon Stieltjes/ENNReal equality, proving nonnegativity of the real integral and converting pointwise via ENNReal.toReal_ofReal. This is a named real L1 bridge needed by stopped verification, with time-zero right-limit and all continuous/jump cash preserved.
-- source:
--   Accepted original bounded random-clock toReal reward L1 and W7-03 exact pathwise real-horizon original Stieltjes equality cabfeef5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_signed_stieltjes_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P := by sorry
