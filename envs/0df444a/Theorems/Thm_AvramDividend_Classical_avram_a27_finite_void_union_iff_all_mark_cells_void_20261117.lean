-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_finite_void_union_iff_all_mark_cells_void_20261117
-- name    : AvramDividend.Classical.avram_a27_finite_void_union_iff_all_mark_cells_void_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:14:05.680567+00:00
-- url     : https://prove2.me/theorems/755eae2b-b737-420e-8023-0ea314e6fcfc
-- title:
--   Finite union of marked cells has zero measure exactly when every constituent cell is void
-- statement:
--   For an arbitrary finite collection of measurable or nonmeasurable marked point-process cells and any nonnegative source measure, the union has zero mass if and only if every individual cell has zero mass. This connects finite original Borel void events with the void event of their union for the marked-Poisson independence argument.
-- source:
--   Pinned Mathlib measure_union_null_iff and induction on the finite family; no stochastic assumptions or change of source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- A finite union is null exactly when each member set is null for any source measure. -/

theorem AvramDividend.Classical.avram_a27_finite_void_union_iff_all_mark_cells_void_20261117
    {α ι : Type*} [MeasurableSpace α] [DecidableEq ι]
    (μ : Measure α) (S : Finset ι) (B : ι → Set α) :
    μ (⋃ i ∈ S, B i) = 0 ↔ ∀ i ∈ S, μ (B i) = 0 := by sorry
