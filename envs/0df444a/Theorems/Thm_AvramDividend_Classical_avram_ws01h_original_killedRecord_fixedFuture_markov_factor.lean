-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_original_killedRecord_fixedFuture_markov_factor
-- name    : AvramDividend.Classical.avram_ws01h_original_killedRecord_fixedFuture_markov_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:12:59.015383+00:00
-- url     : https://prove2.me/theorems/1061aefc-2095-4553-8c89-c9423b46fc57
-- title:
--   Original lower-killed capped first record factors arbitrary measurable full-future Lévy reward
-- statement:
--   For the genuine source Lévy process, arbitrary strict upper and lower barriers, and every finite cap, the original lower-surviving first-record event is independent of the entire post-record future path in the strong-Markov integral sense. Every measurable nonnegative discount depending on the actual capped record time and every measurable nonnegative reward of the entire shifted future path factor exactly, with the true original P law and no artificial tilted path-space assumption. This is the required stopped-history kernel to construct the Esscher random-clock killed renewal.
-- source:
--   The genuine original lower-killed capped-history event was proved by WS01H 3aa8a4e1; its finite stopping-time interface is a source-faithful transport via accepted stoppedHistory_measurable_of_equal_finite_clocks 15c19b45. Actual capped clock stopping and ambient measurability aca9a992, original event ambient measurability 59d0930d, and the accepted original right-continuous whole-future Lévy factor f437c3bd conclude without a two-sided exit formula. Source context Avram–Palmowski–Pistorius (2007), eq. (3.6) stopped first record.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_original_record_survival_stopped_history
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_finiteStopping_discountedFutureReward_factor
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_rightCont_stopping_and_clock_measurable
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_measurable_of_equal_finite_clocks
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_coe_toNNReal_with_measure_import
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_original_killedRecord_fixedFuture_markov_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower b : ℝ) (N : ℝ≥0)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
    let A : Set Ω :=
      {ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
      {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
    (∫⁻ ω, if ω ∈ A then
      discount (τ ω) *
        reward (fun u : ℝ≥0 => X.X (τ ω + u) ω - X.X (τ ω) ω)
      else 0 ∂P) =
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      (∫⁻ ω, reward (fun u : ℝ≥0 => X.X u ω) ∂P) := by sorry
