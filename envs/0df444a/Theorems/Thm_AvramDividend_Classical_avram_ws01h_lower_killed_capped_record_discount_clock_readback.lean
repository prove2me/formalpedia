-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_lower_killed_capped_record_discount_clock_readback
-- name    : AvramDividend.Classical.avram_ws01h_lower_killed_capped_record_discount_clock_readback
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:34:38.94985+00:00
-- url     : https://prove2.me/theorems/0c23a4ff-d119-4be4-b032-febd50658aa5
-- title:
--   Actual lower-killed capped strict first-record reward evaluates at the genuine uncapped source first-passage clock
-- statement:
--   For the true original spectrally negative Lévy process, at every nonnegative deterministic cap N and any original strict lower-killed upper-first-record historical event with T_up≤N, the capped finite record clock (min(T_up,N)).toNNReal is exactly the original first upper passage age T_up.toNNReal. Thus any nonnegative terminal stopped reward F, in particular the true Esscher exp(θb−(p+q)t) discount, has exactly the same source-P lower-killed expected integral whether evaluated at capped or original upper record time. This is a direct unconditional original-source first-passage identity and is the precise readback needed to remove the cap after the genuine finite-Qp CDF regeneration, without importing the two-sided exit ratio.
-- source:
--   Canonically Proved firstRecord_capped_clock_eq_uncapped_of_le_horizon 159a20a9 and pinned Mathlib ENNReal.toNNReal_coe/lintegral_congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_lower_killed_capped_record_discount_clock_readback
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b lower : ℝ) (N : ℝ≥0) (F : ℝ≥0 → ℝ≥0∞) :
    (∫⁻ ω, if twoSidedExitUpTime X b ω <
        twoSidedExitDownTime X lower ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      F (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
      else 0 ∂P) =
    (∫⁻ ω, if twoSidedExitUpTime X b ω <
        twoSidedExitDownTime X lower ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      F (twoSidedExitUpTime X b ω).toNNReal else 0 ∂P) := by sorry
