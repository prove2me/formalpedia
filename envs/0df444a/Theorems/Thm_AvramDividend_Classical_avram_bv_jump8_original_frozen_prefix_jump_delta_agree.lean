-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_frozen_prefix_jump_delta_agree
-- name    : AvramDividend.Classical.avram_bv_jump8_original_frozen_prefix_jump_delta_agree
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:06:38.388867+00:00
-- url     : https://prove2.me/theorems/35e0e72b-4451-4066-a199-54e3324add89
-- title:
--   Exact intrinsic original jump mark coincides with horizon-frozen jump mark at every positive source time through horizon
-- statement:
--   At each strictly positive u≤n, the original and horizon-frozen source Lévy paths have equal jump marks, including at u=n. The positive-time condition excludes the zero-origin atom. Uses exact original leftLimit agreement, no distributional approximation.
-- source:
--   By min_eq_left and Proved 8e873bf7. This pointwise equality is the mark-domain ingredient of the exact original/frozen marked rectangle identity 624daffe.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_original_frozen_prefix_jump_delta_agree
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (n : ℕ) (u : ℝ≥0) (hu : 0 < u) (huN : u ≤ (n : ℝ≥0)) :
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u =
    X.X (min u (n : ℝ≥0)) ω -
      Function.leftLim (fun v : ℝ≥0 => X.X (min v (n : ℝ≥0)) ω) u := by sorry
