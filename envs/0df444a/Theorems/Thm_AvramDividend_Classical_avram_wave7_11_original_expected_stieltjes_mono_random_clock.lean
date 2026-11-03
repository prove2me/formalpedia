-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_stieltjes_mono_random_clock
-- name    : AvramDividend.Classical.avram_wave7_11_original_expected_stieltjes_mono_random_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:04:07.349198+00:00
-- url     : https://prove2.me/theorems/e7ecd078-3f70-43f4-886b-481f83226eea
-- title:
--   Original finite-horizon expected Stieltjes dividend reward monotone in random stopping clock
-- statement:
--   For the genuine original dividendMeasure D ω, if sample-dependent payment clocks σ(ω)≤τ(ω) pointwise, then the expected discounted ENNReal Stieltjes reward on paymentTimes σ(ω)∩Iic T is no more than that for τ(ω), at the same real horizon T. This holds without an extra clock-measurability premise because it is a pointwise set inclusion followed by monotonicity of the original inner and outer integrals.
-- source:
--   Source-faithful original-process random-clock comparison for UBV finite-horizon dividend verification cc518136. The t=0 right dividend atom remains in both payment regions.

import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_expected_stieltjes_mono_random_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ)
    (σ τ : Ω → ℝ≥0∞) (hστ : ∀ ω, σ ω ≤ τ ω)
    (q T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (τ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
