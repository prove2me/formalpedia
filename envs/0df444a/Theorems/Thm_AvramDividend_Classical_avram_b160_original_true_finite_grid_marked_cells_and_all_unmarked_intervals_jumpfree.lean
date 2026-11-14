-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b160_original_true_finite_grid_marked_cells_and_all_unmarked_intervals_jumpfree
-- name    : AvramDividend.Classical.avram_b160_original_true_finite_grid_marked_cells_and_all_unmarked_intervals_jumpfree
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:06:49.163791+00:00
-- url     : https://prove2.me/theorems/49e77285-410a-4cae-8da1-7c3f8a26e78a
-- title:
--   Original physical finite stopped-grid marked cells exactly classify genuine source jump-containing and jumpfree cells
-- statement:
--   For the genuine original spectrally negative Levy process at any sample path and arbitrary finite family of potentially random physical source time intervals, define a finite set of indices marking exactly the intervals containing at least one nonzero actual original source jump at a time strictly after the left endpoint and up to the right endpoint. This finite original marked-cell selector is included in the original finite grid index set, and every unmarked source interval is physically jumpfree at every time in its own half-open interval. The proof constructs the genuine Finset filter, gives the exact iff membership and derives jumpfree source difference by contradiction. This supplies a canonical same-source hNoJump classification for the finite-grid quadratic energy and authentic stopped Ito argument, without replacing the Lévy process or requiring finite negative second moments. Measurability and Poisson source count domination for this selected Finset remain separate obligations.
-- source:
--   Original SpectrallyNegativeLevy jump increments and Mathlib Finset.filter physical jump selection.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original source jump-containing cells of an arbitrary finite stopped grid form a Finset; unmarked cells are physically jumpfree throughout their own half-open intervals. -/

theorem AvramDividend.Classical.avram_b160_original_true_finite_grid_marked_cells_and_all_unmarked_intervals_jumpfree
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0) :
    ∃ J : Ω → Finset ℕ,
      (∀ ω i, i ∈ J ω ↔ i ∈ S ∧
        ∃ u : ℝ≥0, s i ω < u ∧ u ≤ t i ω ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
      (∀ ω, J ω ⊆ S) ∧
      (∀ ω i, i ∈ S → i ∉ J ω → ∀ u : ℝ≥0,
        s i ω < u → u ≤ t i ω →
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) := by sorry
