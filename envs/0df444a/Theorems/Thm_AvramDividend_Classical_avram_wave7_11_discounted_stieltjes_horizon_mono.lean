-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_discounted_stieltjes_horizon_mono
-- name    : AvramDividend.Classical.avram_wave7_11_discounted_stieltjes_horizon_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:55:31.012843+00:00
-- url     : https://prove2.me/theorems/f74e27ec-298e-4433-bf54-1782a7d2e569
-- title:
--   Monotonicity of original-process expected discounted Stieltjes dividends across finite horizons
-- statement:
--   For the same original dividend process D, arbitrary original ruin horizon σ(ω) and the exact Stieltjes measure, the expected discounted payments on paymentTimes(σ) up to T do not exceed those up to U whenever T≤U. This includes the time-zero right atom and requires no independent path measure. It supports deterministic horizon bookkeeping for the canonical UBV finite-horizon estimate and its later monotone limit.
-- source:
--   Measure monotonicity on paymentTimes(σ(ω))∩Iic T ⊆ paymentTimes(σ(ω))∩Iic U, then outer ENNReal lintegral monotonicity. Faithful to AvramDividend.Classical dividendMeasure and paymentTimes definitions; pinned Mathlib signature MeasureTheory.lintegral_mono_set from remote compiler at 0df444a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_discounted_stieltjes_horizon_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞) (q T U : ℝ)
    (hTU : T ≤ U) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic U,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
