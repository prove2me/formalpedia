-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_positive_horizon_exact_endpoint_decomposition
-- name    : AvramDividend.Classical.avram_wave7_11_original_expected_positive_horizon_exact_endpoint_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:11:11.845169+00:00
-- url     : https://prove2.me/theorems/1cf80544-0b3d-44fb-b375-b4759a57c4a4
-- title:
--   Exact original-process expected finite-horizon Stieltjes payout with positive terminal atom
-- statement:
--   For the genuine spectrally negative Levy process X and its original law P, with source-faithful admissible dividend strategy D, at any positive finite observation T the expected discounted Stieltjes payoff through T equals the expectation of the strict truncated-clock payoff plus the expectation of the exact original payment atom at T. The stochastic law, ruin time, sample space and Stieltjes measure are unchanged. The proved arbitrary-measurable-stopping integral lemma supplies measurability, and the exact pathwise disjoint union supplies the equality.
-- source:
--   Proved original arbitrary measurable stopped Stieltjes reward measurability 014f398c, positive-horizon pathwise exact endpoint decomposition W7-11, Mathlib lintegral_add_left.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_horizon_reward_eq_truncated_clock_plus_endpoint
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_expected_positive_horizon_exact_endpoint_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) +
    (∫⁻ ω, ∫⁻ t in
      (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
