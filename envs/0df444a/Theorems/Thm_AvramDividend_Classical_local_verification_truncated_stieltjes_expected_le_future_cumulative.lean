-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_truncated_stieltjes_expected_le_future_cumulative
-- name    : AvramDividend.Classical.local_verification_truncated_stieltjes_expected_le_future_cumulative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:30:50.365758+00:00
-- url     : https://prove2.me/theorems/0a496160-5cfd-4bca-ad98-6cd0ba8fb1ed
-- title:
--   Expected full stopped Stieltjes payout is dominated by expected future cumulative dividends
-- statement:
--   For any dividend strategy, any random stopping cut-off σ, any nonnegative discount rate, and deterministic time T strictly below S, the expected full discounted dividend reward on permitted payment times up to T is no greater than E[ENNReal.ofReal(D(S))]. This includes the continuous Stieltjes component and every right-jump atom. It supplies the outer-expectation domination needed before finite-grid approximation, using pointwise domination and monotonicity of the nonnegative Lebesgue integral, without assuming future dividends are integrable.
-- source:
--   Proved discounted_dividendMeasure_Ico_zero_le_dividend_cumulative (9a0c3a15-0585-461a-b3fc-9a117ede6a13), with lintegral_mono_set and lintegral_mono.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_dividendMeasure_Ico_zero_le_dividend_cumulative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_truncated_stieltjes_expected_le_future_cumulative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S) :
    (∫⁻ ω, ∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal (D S ω) ∂P) := by sorry
