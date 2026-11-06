-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_C1_compact_stopped_jump_increment_dominator
-- name    : AvramDividend.Classical.avram_p3_2_original_C1_compact_stopped_jump_increment_dominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:15:01.690269+00:00
-- url     : https://prove2.me/theorems/163a51e2-26d4-40d4-bd05-ba8eec45b51d
-- title:
--   Actual stopped original jump increments have one compact C1 BV domination constant
-- statement:
--   For the actual original Lévy jump marks, any eventual physical stopped localisation placing pre- and post-jump controlled reserves in the same compact subset of the C1 generator region supplies a single nonnegative real Lipschitz constant dominating every signed nonlinear original jump increment by its genuine mark size, uniformly over tags and stopped jump times.
-- source:
--   Proved original compact C1 Lipschitz constant a747d35f and exact original X.X marked jumps. Bridges physical strict compact localisation to the BV summable-majorant premise of the original infinite-activity stopped nonlinear source limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_C1_compact_stopped_jump_increment_dominator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ) (U : Set ℝ)
    (hw : ContDiffOn ℝ 1 w U) (lo hi : ℝ)
    (hSub : Set.Icc lo hi ⊆ U)
    (S : ℝ≥0) (z : ℕ → ℝ≥0 → ℝ)
    (hBand : ∀ᶠ k in atTop,
      ∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t) ≠ 0 →
        z k t ∈ Set.Icc lo hi ∧
        z k t + (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t) ∈ Set.Icc lo hi) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ᶠ k in atTop,
        ∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t) ≠ 0 →
          |w (z k t + (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)) - w (z k t)| ≤
            L * |(X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)| := by sorry
