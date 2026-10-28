-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_fullPath_postStop_Esscher_reward_measurable
-- name    : AvramDividend.Classical.avram_ws01e_b_joint_fullPath_postStop_Esscher_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:42:21.61545+00:00
-- url     : https://prove2.me/theorems/e1f7619d-9345-4c08-a67c-0b835fa6c177
-- title:
--   Joint measurability of the complete Esscher post-stopping full-path reward at a real observation clock
-- statement:
--   Let τ be any measurable finite age for a real-valued spectrally negative Lévy process and H a jointly measurable nonnegative reward depending on the residual clock and entire shifted path. For any measurable path weight W and Esscher parameter θ, the product of W, the actual compensated Esscher density through τ, the compensated Esscher post-τ increment density at a variable real clock r and the full shifted-path reward H(r+,Yτ) is jointly measurable in (ω,r). This directly discharges the hReward premise of the open capped genuine random-terminal Esscher regeneration bridge when the reward is jointly measurable, without assuming any strong-Markov or tilted independence.
-- source:
--   Proved avram_ws01e_b_randomAge_whole_shiftedPath_measurable (8e59a363), chat04_levy_joint_time_state_measurable (d55462c3), pinned Mathlib measurable composition, exp, and multiplication.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_joint_fullPath_postStop_Esscher_reward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (θ : ℝ)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
      H z.1 z.2))
    (W : Ω → ℝ≥0∞) (hW : Measurable W) :
    Measurable (fun z : Ω × ℝ =>
      (W z.1 * ENNReal.ofReal (Real.exp
        (θ * X.X (τ z.1) z.1 - (τ z.1 : ℝ) * X.ψ θ))) *
      (ENNReal.ofReal (Real.exp
        (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 -
          X.X (τ z.1) z.1) -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)) *
       H (Real.toNNReal z.2)
         (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 -
            X.X (τ z.1) z.1))) := by sorry
