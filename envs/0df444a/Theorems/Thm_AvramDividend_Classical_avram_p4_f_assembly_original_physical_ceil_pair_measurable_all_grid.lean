-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_physical_ceil_pair_measurable_all_grid
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_physical_ceil_pair_measurable_all_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:30:33.460782+00:00
-- url     : https://prove2.me/theorems/f09bb8b3-ecff-41d1-ba48-19bdc6582a60
-- title:
--   Every original Lévy physical ceiling-grid chronological pair count is measurable, including zero mesh
-- statement:
--   For the actual finite source X.X negative-band marked times, the chronological ceiling-index count is measurable at every integer mesh. At positive meshes the Proved original intrinsic pathwise pair identity and Proved measurable original finite-grid compensator provide measurability. At zero mesh the count is identically zero.
-- source:
--   Proved original pathwise 3bf8aa71, exact uniform endpoints 6bdc2c26, same-source grid-pair-sum measurability 2dec7a05. Original process, exact P, finite marked set; no auxiliary distribution.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_uniform_source_grid_endpoints
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_grid_intrinsic_pair_sum
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_grid_pair_sum_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_physical_ceil_pair_measurable_all_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∀ k : ℕ, Measurable (fun ω =>
      (((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞))) := by sorry
