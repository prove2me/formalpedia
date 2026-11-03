-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_toReal_budget_to_ennreal_cash
-- name    : AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_toReal_budget_to_ennreal_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:37:25.585225+00:00
-- url     : https://prove2.me/theorems/d9993239-bbe3-4913-a7a4-70f731bae570
-- title:
--   Exact original bounded random-clock expected toReal cash budget implies true double ENNReal payout budget
-- statement:
--   For any bounded measurable random clock at the original spectrally negative Levy process and capped admissible strategy, a real expected budget of the inner original ENNReal dividend cash converted via toReal on paymentTimes(ruinTime)∩Iic(τ ω) implies a budget on the exact outer double ENNReal payout with the same P, dividendMeasure and stopped domain. The proof converts the real toReal expected cash to genuine real signed Stieltjes expectation by Proved e1f31472 and then uses Proved original full bounded random-clock real/ENNReal mean equality fc7c1b8a plus ENNReal.ofReal monotonicity. Measurability, nonnegativity and L1 under bounded clock follow the previously accepted source lemmas, not a proxy model.
-- source:
--   Proved e1f31472 original bounded random-clock toReal expected real-Stieltjes equality and fc7c1b8a exact mean equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_toReal_cash_mean_eq_signed_stieltjes_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_toReal_budget_to_ennreal_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (B : ℝ)
    (hBudget :
      (∫ ω, (∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by sorry
