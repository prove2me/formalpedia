-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_stieltjes_discount_horizon_comparison
-- name    : AvramDividend.Classical.avram_wave7_11_original_expected_stieltjes_discount_horizon_comparison
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:25:00.218888+00:00
-- url     : https://prove2.me/theorems/4becc910-652a-4db1-b444-b6fa34ddf8e1
-- title:
--   Original expected finite-horizon Stieltjes payout order under discount rate and horizon changes
-- statement:
--   For the original dividendMeasure and original probability P, if the discount rate grows q1≤q2 while the horizon shortens T≤U, the q2-discounted expected Stieltjes reward through T is no greater than the q1-discounted reward through U. The comparison preserves initial and terminal dividend atoms and arbitrary original random stopping clocks.
-- source:
--   Direct combination of Proved expected rate antitonicity 8ecc75cf and expected real-horizon monotonicity 9904fd14; deterministic finite-horizon conversion helper for the Avram UBV value bridge.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_expected_stieltjes_antitone_in_discount_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_stieltjes_horizon_mono

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_expected_stieltjes_discount_horizon_comparison
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (q₁ q₂ T U : ℝ) (hq : q₁ ≤ q₂) (hTU : T ≤ U) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q₂ * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic U,
      ENNReal.ofReal (Real.exp (-(q₁ * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
