-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b94_original_exact_finite_grid_negative_mark_cell_selection
-- name    : AvramDividend.Classical.avram_b94_original_exact_finite_grid_negative_mark_cell_selection
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T14:30:57.482817+00:00
-- url     : https://prove2.me/theorems/8a8bbbfe-66ef-46a5-8190-f51b36bb8bf6
-- title:
--   Exact original-source physical marking of finite stopped cells and proof that every unmarked cell is truly jumpfree
-- statement:
--   Construct the actual sample-path marked-cell set by filtering a finite set of source grid indices S according to existence of a nonzero original Levy left-limit jump in the half-open physical interval (s_i,t_i]. Membership is equivalent to the actual physical source event for every path. The unmarked cells have no source jump anywhere in their intervals. This makes the source nojump input for the small and large negative compensated increment lemmas constructive, with no fictitious independent Gaussian process. Measurability and marked-cardinality domination remain separate obligations.
-- source:
--   Physical original SpectrallyNegativeLevy source and exact finite grid filter, preceding Avram Palmowski Pistorius Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The marked finite cells are exactly those containing a source jump. -/

theorem AvramDividend.Classical.avram_b94_original_exact_finite_grid_negative_mark_cell_selection
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0) :
    ∃ J : Ω → Finset ℕ,
      (∀ ω i, i ∈ J ω ↔ i ∈ S ∧
        ∃ u : ℝ≥0, s i ω < u ∧ u ≤ t i ω ∧
          X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
      (∀ ω i, i ∈ S → i ∉ J ω →
        ∀ u : ℝ≥0, s i ω < u → u ≤ t i ω →
          X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) := by sorry
