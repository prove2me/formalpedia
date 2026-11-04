-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_finite_grid_equal_cell_means_lintegral
-- name    : AvramDividend.Classical.avram_wave7_06_finite_grid_equal_cell_means_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:04:28.456203+00:00
-- url     : https://prove2.me/theorems/da5bd81d-4339-42c8-9b59-15261bcb50be
-- title:
--   Expected occupied grid-cell count is the number of cells times the single-cell mean
-- statement:
--   For a finite family of measurable original-space nonnegative occupied-cell variables with equal means q, the expected total occupied count is m q. This finite-grid identity needs no independence and combines with source one-cell occupation probability to supply the small-time void intensity slope before taking the dominated-convergence limit.
-- source:
--   W7-06 original Lévy finite marked-grid mean assembly, pinned lintegral_finset_sum.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave7_06_finite_grid_equal_cell_means_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ)
    (F : ℕ → Ω → ENNReal) (q : ENNReal)
    (hMeas : ∀ i ∈ Finset.range m, Measurable (F i))
    (hEach : ∀ i ∈ Finset.range m, (∫⁻ ω, F i ω ∂P) = q) :
    (∫⁻ ω, ∑ i ∈ Finset.range m, F i ω ∂P) =
      (m : ENNReal) * q := by sorry
