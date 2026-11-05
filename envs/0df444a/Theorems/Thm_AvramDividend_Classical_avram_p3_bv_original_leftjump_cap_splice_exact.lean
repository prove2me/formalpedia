-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_leftjump_cap_splice_exact
-- name    : AvramDividend.Classical.avram_p3_bv_original_leftjump_cap_splice_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:54:32.09653+00:00
-- url     : https://prove2.me/theorems/6d91b7e7-7a24-4b46-80dc-3b9759ed240e
-- title:
--   Original positive-time Lévy left jump preserves exact finite/infinite-cap candidate increment
-- statement:
--   For every actual positive-time jump of the original spectrally negative Lévy X and every pre-jump candidate reserve below the finite cap, the cap-spliced C1 function V and the original w have the same value increment across the source jump, including ruin-crossing jumps. This follows from the source-exact no-positive-jump sign theorem and the proved cap-splice identity; the infinite-cap case is automatic. This helps substitute the true source left jumps into the BV stopped grid identity without a fabricated process law.
-- source:
--   Proved original raw left-jump sign 561ccef5-08ed-4169-b930-9bd8544810a6; Proved frozen cap-splice identity d4d6eb3b-4bef-43b1-b174-91ce04e359e6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_frozen_source_cap_splice_step

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_bv_original_leftjump_cap_splice_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ v : ℝ, V v = w v)
    (hVfinite : C ≠ ⊤ → ∀ v : ℝ,
      V v = if v ≤ C.toReal then w v
        else w C.toReal + (v - C.toReal))
    (z : ℝ) (hz : C = ⊤ ∨ z ≤ C.toReal) :
    V (z + (X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)) - V z =
      w (z + (X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)) - w z := by sorry
