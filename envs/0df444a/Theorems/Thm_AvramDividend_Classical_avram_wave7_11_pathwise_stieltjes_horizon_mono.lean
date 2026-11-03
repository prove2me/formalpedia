-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_pathwise_stieltjes_horizon_mono
-- name    : AvramDividend.Classical.avram_wave7_11_pathwise_stieltjes_horizon_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:49:35.669526+00:00
-- url     : https://prove2.me/theorems/30874edf-42e5-4855-a9bd-607e8d2a8b7a
-- title:
--   Original pathwise complete Stieltjes dividend reward is monotone in the real horizon
-- statement:
--   For every original dividend strategy path D ω, canonical paymentTimes σ and real finite horizons T≤U, the ENNReal integral of discounted dividend Stieltjes payments over paymentTimes σ∩Iic T is no greater than that over paymentTimes σ∩Iic U. The proof is exact set inclusion and monotonicity of the genuine Stieltjes measure, with t=0 and horizon endpoint included.
-- source:
--   Pathwise strengthening of earlier Proved outer expectation horizon monotonicity f74e27ec. Separates deterministic time-set inclusion from probability expectation in UBV finite-horizon bridge cc518136.

import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_pathwise_stieltjes_horizon_mono
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q T U : ℝ) (hTU : T ≤ U) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in paymentTimes σ ∩ Iic U,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
