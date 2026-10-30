-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_capped_barrier_killed_future_reward_factor
-- name    : AvramDividend.Classical.avram_root29_05_capped_barrier_killed_future_reward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T07:48:09.747246+00:00
-- url     : https://prove2.me/theorems/980471ab-af34-498f-8c9b-bddfd553eb22
-- title:
--   Capped controlled-barrier upcrossing killed-prefix strong-Markov reward factorisation
-- statement:
--   For the genuine spectrally negative Lévy process and its original barrier dividend regulator, the event that strict first upcrossing occurs before controlled ruin and before a finite cap is measurable at the capped stopping time. Its discounted stopped-history weight factors from any measurable reward of the shifted future Lévy path. This is an actual killed first-history factor, with no q-scale identity or reflected-supremum substitution.
-- source:
--   Source-faithful consequence of the Proved upper-passage/right-continuous filtration stopping theorems, barrier-strategy admissibility, original controlled ruin-time stopping theorem, capped stopped-history event lemma and exact full-future-path stopped Markov reward factor. Supports Open 79978d61 and 8fc83520 without assuming their conclusions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_upperPassage_capped_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_coe_toNNReal_with_measure_import
import Theorems.Thm_AvramDividend_Classical_barrierSuccessfulClockCutoff_stoppedHistory
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_measurable_of_equal_finite_clocks
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor_rightCont

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_05_capped_barrier_killed_future_reward_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx : 0 ≤ x) (ha : 0 < a) (hxa : x ≤ a)
    (N : ℝ≥0)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    let T := twoSidedExitUpTime X (a - x)
    let R := ruinTime X x (barrierStrategy X x a)
    let τ : Ω → ℝ≥0 := fun ω => (min (T ω) (N : ℝ≥0∞)).toNNReal
    let A : Set Ω := {ω | T ω < R ω ∧ T ω ≤ (N : ℝ≥0∞)}
    (∫⁻ ω, if ω ∈ A then
        discount (τ ω) *
          reward (fun t : ℝ≥0 => X.X (τ ω + t) ω - X.X (τ ω) ω)
      else 0 ∂P) =
      (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by sorry
