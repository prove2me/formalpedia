-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pairs_strict_mesh_equiv
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_marked_pairs_strict_mesh_equiv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:47:29.309437+00:00
-- url     : https://prove2.me/theorems/e2763a92-b517-4aa9-a39d-10a6af1b6737
-- title:
--   Chronological original negative-band jump pairs equal strictly indexed uniform-grid pairs
-- statement:
--   For the literal original negative-band finite marked-time set at a positive horizon, one uniform grid has the property that its ceiling index strictly preserves and reflects chronological order on all marked pairs. This is the pair-set equality needed to compare the original pathwise ordered-pair count with finite-grid cross counts.

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pair_strict_mesh_index
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_marked_pairs_strict_mesh_equiv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k : ℕ, 0 < k ∧
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)) =
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))) := by sorry
