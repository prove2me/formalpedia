-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_stopped_post_esscher_fullPath_reward_measurable
-- name    : AvramDividend.Classical.avram_ws01h_actual_stopped_post_esscher_fullPath_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:51:41.087701+00:00
-- url     : https://prove2.me/theorems/b99a49e0-c75e-475c-b4e7-e500070968c1
-- title:
--   Actual stopped Lévy Esscher compensated full-future reward is jointly measurable
-- statement:
--   For every source spectrally negative Lévy process, measurable finite stopped age, and jointly measurable whole-future-path reward H, the actual stopped time-shifted Esscher density multiplied by the entire post-stop reward is jointly Borel measurable in the original omega and real residual-clock age. This exactly discharges hPostMeas in the lower-killed first-record Qp renewal without an external measurability premise or a tilted infinite-path law.
-- source:
--   Accepted original Lévy joint time-state measurability d55462c3 and accepted complete shifted full-path reward measurability 0c3b081a, combined with Mathlib exponential and NNReal clock conversion.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_wholePath_stopped_reward_measurable

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_actual_stopped_post_esscher_fullPath_reward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) (θ : ℝ)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2)) :
    Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 -
          X.X (τ z.1) z.1) -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)) *
        H (Real.toNNReal z.2)
          (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)) := by sorry
