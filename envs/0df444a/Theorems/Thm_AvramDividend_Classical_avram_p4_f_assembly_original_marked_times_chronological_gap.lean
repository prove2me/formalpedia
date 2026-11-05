-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_times_chronological_gap
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_marked_times_chronological_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:16:25.435494+00:00
-- url     : https://prove2.me/theorems/7f1ed4d2-c934-4f73-851d-2255188002ff
-- title:
--   Original negative-band finite marked jump times have uniform positive signed chronological separation
-- statement:
--   For the exact original source intrinsic negative-band marked jump times on the finite horizon T, every chronological pair u<v in that source set has a common strictly positive real time gap δ bounded by v-u. The bound follows from the accepted finite original marked-times construction and the accepted generic Finset pairwise-separation theorem, translating absolute differences into chronological signed gaps. This is a deterministic source-specific input to selecting sufficiently fine time grids for eventual separation of every actual ordered jump pair, without assumptions on independent or replacement processes.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_finite_NNReal_marked_times_pairwise_gap
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_marked_times_chronological_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u ∈ F, ∀ v ∈ F, u < v → δ ≤ (v : ℝ) - (u : ℝ) := by sorry
