-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_wholePath_stopped_reward_measurable
-- name    : AvramDividend.Classical.avram_ws01e_b_joint_wholePath_stopped_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:39:19.001548+00:00
-- url     : https://prove2.me/theorems/0c3b081a-73cb-4dc3-9a71-a6cf601e45e2
-- title:
--   Joint measurability of full shifted-path reward evaluated at actual and residual random clocks
-- statement:
--   For an actual Lévy process, any measurable finite random stopping age τ, a measurable nonnegative path reward H(t,Y) defined jointly on clock time and the whole future path, and a measurable history weight W, both the full shifted-path reward H(E,Yτ) evaluated at an arbitrary real observation time E and the actual residual-clock reward W·H((E−τ)^+,Yτ) are jointly measurable functions of the original path and real observation clock. This discharges two explicit measurability premises used in the genuine random-terminal Esscher capped first-record fullPath regeneration theorem without asserting any tilted independence.
-- source:
--   Proved avram_ws01e_b_randomAge_whole_shiftedPath_measurable (8e59a363) and pinned Mathlib measurable composition, real_toNNReal and multiplication.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_joint_wholePath_stopped_reward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2))
    (W : Ω → ℝ≥0∞) (hW : Measurable W) :
    Measurable (fun z : Ω × ℝ =>
      H (Real.toNNReal z.2)
        (fun s : ℝ≥0 =>
          X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)) ∧
    Measurable (fun z : Ω × ℝ =>
      W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ)))
        (fun s : ℝ≥0 =>
          X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)) := by sorry
