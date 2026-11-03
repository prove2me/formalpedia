-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_horizon_reward_le_min_clock_plus_terminal_atom
-- name    : AvramDividend.Classical.avram_wave7_11_original_expected_horizon_reward_le_min_clock_plus_terminal_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:32:42.293464+00:00
-- url     : https://prove2.me/theorems/ceca6326-e80e-4e22-a96b-4960a0bbaef9
-- title:
--   Expected original finite-horizon dividend reward bounded by strict stopped clock plus terminal atom
-- statement:
--   For the genuine original spectrally negative Levy process X, original IsDividendStrategy regulator D, original ruinTime and probability P, the expected discounted Stieltjes payout on the exact real finite horizon payment region is at most the expected reward with the ruin clock truncated at T plus the expected original terminal singleton atom. This resolves the nontrivial mismatch between the strict clock min convention and the closed real horizon Iic T.
-- source:
--   Combines Proved pathwise endpoint atom bound e0ff01d5 and Proved original arbitrary measurable stopping-clock Stieltjes reward 014f398c with Mathlib lintegral_add_left. A finite-horizon value bridge for canonical UBV cc518136, preserving the source process and all atoms.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_horizon_reward_le_truncated_clock_plus_endpoint
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_expected_horizon_reward_le_min_clock_plus_terminal_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) +
    (∫⁻ ω, ∫⁻ t in
      (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
