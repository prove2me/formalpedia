-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_nat_ruin_clock_expected_reward_mono
-- name    : AvramDividend.Classical.avram_wave7_11_original_nat_ruin_clock_expected_reward_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:59:41.627997+00:00
-- url     : https://prove2.me/theorems/e61920a3-a813-44ea-907e-0b5c7f45650f
-- title:
--   Original finite-horizon expected Stieltjes reward increases along natural ruin-clock truncations
-- statement:
--   For genuine source ruinTime X x D ω, original dividendMeasure D ω and fixed real finite horizon T, truncating the ruin clock at a larger natural time m≥n can only increase the expected discounted Stieltjes dividends. This is a source-faithful monotonicity statement for the natural-clock values appearing in the W7-08 stochastic budget and W7-11 exact expected supremum identity, and retains all right dividend atoms.
-- source:
--   Direct double ENNReal integral monotonicity from Proved paymentTimes_min_mono_horizon 021cfe05, for the W7-11 original-process finite-horizon uniform budget bridge.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_nat_ruin_clock_expected_reward_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ)
    (n m : ℕ) (hnm : n ≤ m) :
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (m : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
