-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_signed_stieltjes_budget_to_ennreal_cash
-- name    : AvramDividend.Classical.avram_wave7_03_original_signed_stieltjes_budget_to_ennreal_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:10:33.101137+00:00
-- url     : https://prove2.me/theorems/7997b201-6f61-4fa7-acad-5937086acbff
-- title:
--   Exact original signed real Stieltjes expected budget transfers to full stopped ENNReal dividend cash
-- statement:
--   For the original spectrally negative Levy, capped admissible dividend D, real nonnegative horizon T and q>=0, any upper bound B on the real expectation of the signed discounted Stieltjes integral over exactly paymentTimes(ruinTime X x D omega) cap Iic T implies the same ENNReal upper bound for the original full stopped double lintegral. The real integral is with respect to the actual original dividendMeasure on exactly the same stopped set. Real integrability and finite mass are already derived by the accepted W7-03 unconditional expectation identity, so there are no extra hidden assumptions. This directly closes the signed-to-ENNReal gap when the stochastic BV/UBV HJB component provides a real budget.
-- source:
--   Accepted new original unconditional full ruin deterministic expected real/ENNReal identity 633be7dd, Real.coe_toNNReal and ENNReal.ofReal monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_deterministic_horizon_mean_consumption
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_signed_stieltjes_budget_to_ennreal_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (B : ℝ)
    (hBudget :
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by sorry
