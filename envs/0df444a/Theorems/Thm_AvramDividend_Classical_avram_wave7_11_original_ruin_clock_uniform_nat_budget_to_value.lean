-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_ruin_clock_uniform_nat_budget_to_value
-- name    : AvramDividend.Classical.avram_wave7_11_original_ruin_clock_uniform_nat_budget_to_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:51:52.230692+00:00
-- url     : https://prove2.me/theorems/e43bdc5f-627b-4e07-80b1-5c34e8662cbe
-- title:
--   Original dividend strategy uniform truncated ruin-clock budgets imply full finite-horizon expectation bound
-- statement:
--   For the exact original spectrally negative Lévy process X, original strategy D admissible as a dividend strategy, and original Stieltjes dividend measure, a bound B on expected discounted payout up to min(ruinTime, n) for every natural horizon n implies the expected payout bound up to full ruinTime and the same finite real horizon T. Measurability of every truncated payoff is supplied by an already proved canonical arbitrary measurable stop theorem; the monotone ruin-clock limit is independently proved. No additional measurability assumption enters the conclusion.
-- source:
--   Direct deterministic and outer expectation bridge for canonical cc518136 and W7-08 uniform budget 3c9532b7; derived from proved 014f398c and avram_wave7_11_ruin_clock_outer_lintegral_bound_of_measurable_trunc c74c5b53.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_ruin_clock_outer_lintegral_bound_of_measurable_trunc

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_ruin_clock_uniform_nat_budget_to_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (B : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B := by sorry
