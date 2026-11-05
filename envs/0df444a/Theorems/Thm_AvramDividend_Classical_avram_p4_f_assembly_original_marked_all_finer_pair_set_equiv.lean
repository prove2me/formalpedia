-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_all_finer_pair_set_equiv
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_marked_all_finer_pair_set_equiv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:33:40.57771+00:00
-- url     : https://prove2.me/theorems/91dbf8f2-66ca-4d87-a470-35bdad2fc618
-- title:
--   Every sufficiently fine source-uniform grid recovers the exact chronological marked pair set
-- statement:
--   For each original Lévy path the finite original negative-band jump set has a pathwise threshold k0 such that for every k≥k0, the set of strict chronological original marked jump pairs is exactly the set of pairs with strictly increasing ceiling mesh indices. This is the eventual pointwise equality needed for an original-process Fatou argument, requiring no monotonicity between distinct grids.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pairs_all_finer_mesh_indices
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_marked_all_finer_pair_set_equiv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)) =
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))) := by sorry
