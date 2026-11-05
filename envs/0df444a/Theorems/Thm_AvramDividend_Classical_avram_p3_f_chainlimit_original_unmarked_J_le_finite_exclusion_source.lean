-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_unmarked_J_le_finite_exclusion_source
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_unmarked_J_le_finite_exclusion_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:45:29.77545+00:00
-- url     : https://prove2.me/theorems/7c4090f3-d78f-4734-b4a4-e946dd465199
-- title:
--   Original BV unmarked physical grid jump mass bounded by exact finite-exclusion source tail
-- statement:
--   On one P-full event for the genuine original bounded-variation spectrally negative Lévy process, fix finitely many actual positive-time source jumps and injectively tag distinct physical right-closed mesh cells containing them. Then the total original negative-jump mass in the unmarked cells is at most the complete original source jump mass on the observed interval minus the selected finite true-jump magnitudes. The right-hand side is the exact source finite-exclusion tail, which the earlier Proved original BV summability cutoff can make arbitrarily small. This is the genuine missing pathwise cell-mass partition, independent of generator compensation and any assumed stopped chain inequality. The P3-G owner must supply fine-mesh injective tag placement.
-- source:
--   Three fresh source-specific Proved P3-F helpers: original source atom≤J cell, finite injective mark-cell capture, and exact true J grid partition; actual leftLimit X.X and (u_i,u_(i+1)] chronology.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_positive_atom_le_actual_J_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_finite_atom_cell_capture
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_negative_jump_unmarked_grid_partition
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_unmarked_J_le_finite_exclusion_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (T : Finset ℝ≥0) (tag : ℝ≥0 → ℕ)
    (hTag : ∀ v ∈ T, tag v < n)
    (hInj : ∀ v ∈ T, ∀ z ∈ T, tag v = tag z → v = z)
    (hInside : ∀ v ∈ T, u (tag v) < v ∧ v ≤ u (tag v + 1)) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s - X.X s ω
        else 0
      let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
      (∑ i ∈ Finset.range n, if i ∈ T.image tag then 0 else j i) ≤
        J (u n) - J (u 0) -
          (∑ v ∈ T, (Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω)) := by sorry
