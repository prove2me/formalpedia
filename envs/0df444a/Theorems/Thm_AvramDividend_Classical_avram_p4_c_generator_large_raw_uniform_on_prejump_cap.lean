-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_large_raw_uniform_on_prejump_cap
-- name    : AvramDividend.Classical.avram_p4_c_generator_large_raw_uniform_on_prejump_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:06:14.658409+00:00
-- url     : https://prove2.me/theorems/36d694ee-0281-49ae-a316-489d0277a5cb
-- title:
--   Original negative-jump raw payoff uniformly bounded on a nonnegative capped reserve region
-- statement:
--   A payoff continuous on nonnegative reserves and zero on negative reserves is uniformly bounded in absolute value under all negative jumps when the original pre-jump reserve lies in a fixed finite cap [0,v]. This handles jump overshoots without assuming interior C² at the post-jump state, and combines with finite ν mass for jumps z<-epsilon to control the raw large-jump integrand on a localised clock.
-- source:
--   Original source payoff hypotheses hw_cont on Ici 0 and hw_neg on negative states; pinned Mathlib IsCompact.exists_bound_of_continuousOn; negative-jump geometry

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_large_raw_uniform_on_prejump_cap
    (w : ℝ → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ y ∈ Icc 0 v, ∀ z : ℝ, z < 0 →
        |w (y + z) - w y| ≤ M := by sorry
