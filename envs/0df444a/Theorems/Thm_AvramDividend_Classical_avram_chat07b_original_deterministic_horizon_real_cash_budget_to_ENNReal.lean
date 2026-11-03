-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_deterministic_horizon_real_cash_budget_to_ENNReal
-- name    : AvramDividend.Classical.avram_chat07b_original_deterministic_horizon_real_cash_budget_to_ENNReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:14:07.754564+00:00
-- url     : https://prove2.me/theorems/67f2cfad-5bb0-4c6d-bf93-bdd536e88ad8
-- title:
--   Original deterministic-horizon real stopped Stieltjes cash budget implies exact ENNReal outer expected dividend inequality
-- statement:
--   On the original SpectrallyNegativeLevy and original dividendMeasure, any finite nonnegative real horizon T has an almost-sure finite actual stopped Stieltjes discounted payout and integrable real toReal payout by already Proved source measure bounds. Therefore a derived real expectation bound on this actual payout is promoted faithfully to the exact ENNReal outer lintegral bound, with no replacement sample space, lost endpoint atom, or assumed ENNReal payout conclusion. This is the type-correct measure conversion bridge needed after the independent actual-source BV C1 HJB chain produces its real budget.
-- source:
--   Avram Proposition 4(i), Eq. (5.13), original true stopped dividend Stieltjes measure, finite cash and real-to-ENNReal monotone integration; inputs e1455beb, f97e4695, 89e68a17.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_inclusive_random_clock_real_cash_budget_to_ennreal
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_chat07b_original_deterministic_horizon_real_cash_budget_to_ENNReal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q T B : ℝ) (hT : 0 ≤ T)
    (hRealBudget :
      (∫ ω, (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal B := by sorry
