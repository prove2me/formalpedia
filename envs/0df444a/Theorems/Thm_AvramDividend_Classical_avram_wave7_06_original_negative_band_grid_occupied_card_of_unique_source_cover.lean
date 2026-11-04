-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_grid_occupied_card_of_unique_source_cover
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_grid_occupied_card_of_unique_source_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:18:42.827823+00:00
-- url     : https://prove2.me/theorems/f91e8cd4-1dc0-4bde-9bf1-6880489ff66c
-- title:
--   Actual original negative-band jump count equals the number of occupied time-grid cells under a unique-cover certificate
-- statement:
--   For the exact original source Lévy jump times in a negative mark band, if a finite set of grid cells covers all source marked times, each cell contains at most one, and each source time belongs to only one cell, the genuine intrinsic count equals the occupied grid cell cardinal. Compact pathwise finiteness is obtained from an accepted source theorem. This is the exact pathwise ingredient of the law-of-small-numbers Poisson rate derivation.
-- source:
--   W7-06 original marked-count grid occupation, no surrogate Poisson process; auxiliary discrete combinatorial bijection is kernel checked.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_grid_occupied_card_of_unique_source_cover
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (k m : ℕ) (grid : ℕ → ℝ≥0)
    (S : Set ℝ≥0)
    (hS : S = {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -(1 / ((k : ℝ) + 1))})
    (hCover : ∀ u : ℝ≥0, u ∈ S →
      ∃ i : ℕ, i < m ∧ u ∈ Ioc (grid i) (grid (i + 1)))
    (hSingle : ∀ i : ℕ, i < m → ∀ u v : ℝ≥0,
      u ∈ S → v ∈ S →
      u ∈ Ioc (grid i) (grid (i + 1)) →
      v ∈ Ioc (grid i) (grid (i + 1)) → u = v)
    (hIndexUnique : ∀ u : ℝ≥0, u ∈ S → ∀ i j : ℕ,
      i < m → j < m →
      u ∈ Ioc (grid i) (grid (i + 1)) →
      u ∈ Ioc (grid j) (grid (j + 1)) → i = j) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((k : ℝ) + 1)))) =
    (((Finset.range m).filter (fun i =>
      ∃ u : ℝ≥0, u ∈ S ∧ u ∈ Ioc (grid i) (grid (i + 1)))).card :
        ℝ≥0∞) := by sorry
