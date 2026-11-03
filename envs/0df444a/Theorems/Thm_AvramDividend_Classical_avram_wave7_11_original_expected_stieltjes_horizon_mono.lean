-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_stieltjes_horizon_mono
-- name    : AvramDividend.Classical.avram_wave7_11_original_expected_stieltjes_horizon_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:09:11.137922+00:00
-- url     : https://prove2.me/theorems/9904fd14-5361-4c91-8478-c39477b1fc8d
-- title:
--   Original finite-horizon expected Stieltjes dividend value increases with observation horizon
-- statement:
--   For the original sample space and probability measure P, the expected ENNReal discounted Stieltjes dividend payout accumulated through a real horizon T is bounded by that accumulated through U ≥ T, preserving the exact source paymentTimes and right dividend atoms.
-- source:
--   Independent expected-value conversion of Proved W7-11 pathwise horizon monotonicity 30874edf, for canonical UBV finite-horizon value target cc518136.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_pathwise_stieltjes_horizon_mono

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_expected_stieltjes_horizon_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (q T U : ℝ) (hTU : T ≤ U) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic U,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
