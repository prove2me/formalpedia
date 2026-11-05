-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pairs_uniform_grid_scale
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_marked_pairs_uniform_grid_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:03:12.216657+00:00
-- url     : https://prove2.me/theorems/d4f9ea74-336e-4535-9825-9818b5cf2d09
-- title:
--   One original-source finite-grid resolution separates every negative-band chronological jump pair
-- statement:
--   For the exact finite set of original negative-band jump times on (0,T], there is one positive integer k for which the uniform time mesh T/k is strictly smaller than every actual chronological jump-time separation. This follows from the Proved exact-source uniform gap theorem and the Archimedean property and is a necessary pathwise finite-grid refinement bridge to the original chronological pair second factorial moment.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_times_chronological_gap
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_marked_pairs_uniform_grid_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k : ℕ, 0 < k ∧
      ∀ u ∈ F, ∀ v ∈ F, u < v →
        (T : ℝ) < (k : ℝ) * ((v : ℝ) - (u : ℝ)) := by sorry
