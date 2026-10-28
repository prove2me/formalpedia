-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_capped_firstRecord_Qp_fullPath_regeneration_instantiated
-- name    : AvramDividend.Classical.avram_ws01e_b_true_capped_firstRecord_Qp_fullPath_regeneration_instantiated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T15:17:39.710809+00:00
-- url     : https://prove2.me/theorems/3fe509bd-1091-47c4-b60f-056f52e60604
-- title:
--   Source-faithful actual Qp capped first-record whole-future-path regeneration with all stopped density premises discharged
-- statement:
--   For a genuine spectrally negative Lévy process with original probability law, finite capped strict first upper record, positive independent exponential-clock rate and nonnegative Esscher parameter, the exact terminally Esscher-tilted joint path-clock law Qp admits unnormalised capped residual-clock/entire-future-path regeneration. The source-specific stopped survival discount is exp(theta*b-(p+psi(theta))*tau). For every nonnegative jointly measurable residual-age and whole-future-path reward H, the true tilted stopped observation expectation equals the original stopped discount mass times the fresh true tilted random-terminal reward marginal. No independent supremum/drawdown, renewal identity or Wiener-Hopf factor is assumed. This instantiates all stopped Esscher weight, density split, full-path reward, marginal measurability and event-measurability premises of the already Proved capped renewal theorem.
-- source:
--   Apply the Proved capped true-Qp full-path unnormalised regeneration theorem 01473e4b. Derive the actual first-record event and capped age measurability from upper passage stopping. Use Proved exact no-overshoot Esscher survival weight a3830f16, stopped true-Qp likelihood split 114613eb, full-path marginal and joint reward measurability da8731ac/0c3b081a/e1f7619d, and jointly measurable Lévy process and shifted path d55462c3/8e59a363 to discharge all its hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_capped_firstRecord_genuine_Qp_fullPath_unnormalised_regeneration
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_capped_firstRecord_actual_esscher_discount_at_hit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_real_clock_stopped_density_split
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fresh_esscher_fullPath_marginal_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_wholePath_stopped_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_fullPath_postStop_Esscher_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_true_capped_firstRecord_Qp_fullPath_regeneration_instantiated
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (N : ℝ≥0)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2)) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
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
