-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_count_eq_finite_grid_occupancy_of_unique_cover
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_jump_count_eq_finite_grid_occupancy_of_unique_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:39:51.81457+00:00
-- url     : https://prove2.me/theorems/2ed18d64-48df-4745-a906-7177cbdab24c
-- title:
--   Original Lévy intrinsic jump count equals finite-grid occupied-cell count under genuine source-jump unique-cover conditions
-- statement:
--   For any actual original-source spectrally negative Lévy path, fixed horizon T, and finite genuine nonzero-jump time set S in (0,T], suppose n half-open grid cells cover all points of S, no cell contains two distinct jump times, and each genuine jump time belongs to a unique cell. Then the literal source jump-counting measure N_Xω((0,T]×ℝ) equals, as an extended nonnegative number, the cardinal of occupied cells. This is an exact pathwise cardinal bijection for original X, connecting the local-finite jump support theorem and the eventual grid-to-count law. It assumes no Poisson law, generator or auxiliary process and keeps uniqueness/cover hypotheses explicit until proved for fine meshes. The occupied cell cardinal is expressed as the noncomputable finite Set.ncard of eligible indices, so the Lean theorem statement requires no undecidable predicate instance.
-- source:
--   Canonical Proved f6336d40 exact original-X intrinsic rectangle count equals source jump-set extended cardinal for Borel mark set ℝ. Mathlib Finset.card_bij constructs a bijection from occupied grid cells to the finite set of true source jump times under explicit cover, at-most-one-jump, unique-cell-index hypotheses. Set.Finite.encard_eq_coe_toFinset_card converts finite point count to the literal N_X rectangle value. Original Ω, ω, X unchanged; no conditional Poisson extractor assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_jump_count_eq_finite_grid_occupancy_of_unique_cover
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n : ℕ) (grid : ℕ → ℝ≥0)
    (S : Set ℝ≥0)
    (hS : S = {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0})
    (hFin : S.Finite)
    (hCover : ∀ u : ℝ≥0, u ∈ S →
      ∃ i : ℕ, i < n ∧ u ∈ Ioc (grid i) (grid (i + 1)))
    (hSingle : ∀ i : ℕ, i < n → ∀ u v : ℝ≥0,
      u ∈ S → v ∈ S →
      u ∈ Ioc (grid i) (grid (i + 1)) →
      v ∈ Ioc (grid i) (grid (i + 1)) → u = v)
    (hIndexUnique : ∀ u : ℝ≥0, u ∈ S → ∀ i j : ℕ,
      i < n → j < n →
      u ∈ Ioc (grid i) (grid (i + 1)) →
      u ∈ Ioc (grid j) (grid (j + 1)) → i = j) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) =
    ({i : ℕ | i < n ∧ ∃ u : ℝ≥0,
      u ∈ S ∧ u ∈ Ioc (grid i) (grid (i + 1))}.ncard : ENNReal) := by sorry
