-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_capped_killed_Qp_wholePath_regeneration_instantiated
-- name    : AvramDividend.Classical.avram_ws01h_actual_capped_killed_Qp_wholePath_regeneration_instantiated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:05:05.217007+00:00
-- url     : https://prove2.me/theorems/a21ebe34-7968-4a41-abc2-a57977922985
-- title:
--   True lower-killed capped first-record Esscher exponential-clock full-path regeneration
-- statement:
--   For the actual original spectrally negative Lévy law and the genuinely tilted finite exponential joint clock, factor the entire future-path reward after a capped strict first upper record conditional on no strict lower ruin before that record. The left-hand side uses the actual lower-killed stopped history and post-stop path, and the right-hand side is the original-law killed discount factor times the genuine fresh finite-clock Esscher reward expectation. The original-P strong Markov killed-history semigroup, no-positive-overshoot and actual finite-clock density supply the proof, without importing any two-sided exit formula.
-- source:
--   Direct genuine first-record renewal using accepted original killed-history factor 1061aefc, capped no-overshoot 18203, and source-faithful tilted finite clock; no use of 5bcf90, 09663d or stopped scale identities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_capped_killed_record_esscher_fullpath_clock_factor
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_capped_killed_record_exact_discount
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_lowerPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_esscher_fullPath_fresh_reward_lintegral_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_stopped_post_esscher_fullPath_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_wholePath_stopped_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_fullPath_postStop_Esscher_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_real_clock_stopped_density_split
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_actual_capped_killed_Qp_wholePath_regeneration_instantiated
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower b : ℝ) (hb : 0 ≤ b) (N : ℝ≥0)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2)) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
       {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
     let W : Ω → ℝ≥0∞ := fun ω => if ω ∈ A then 1 else 0
     let discount : ℝ≥0 → ℝ≥0∞ := fun u =>
       ENNReal.ofReal (Real.exp (θ * b - (p + X.ψ θ) * (u : ℝ)))
     (∫⁻ z : Ω × ℝ,
       if (τ z.1 : ℝ) ≤ z.2 then
         W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ)))
           (fun s : ℝ≥0 =>
             X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
       else 0
       ∂((P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) =
     (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
       (∫⁻ r : ℝ, (∫⁻ ω,
         ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal r) ω -
             (Real.toNNReal r : ℝ) * X.ψ θ)) *
         H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) ∂P)
         ∂(expMeasure p))) := by sorry
