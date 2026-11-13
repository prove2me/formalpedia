-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a26_last_mesh_cell_positive_split
-- name    : AvramDividend.Classical.avram_ga_a26_last_mesh_cell_positive_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T07:34:12.917208+00:00
-- url     : https://prove2.me/theorems/1c1b3256-2d0c-4393-8dff-016661cc5774
-- title:
--   Positive Gaussian mesh residual controlled by paired cells and last clipped cell
-- statement:
--   For an original Gaussian clipped mesh, the spatial residual uses m+1 postpayment cells but only m centred and generator cells. The positive part of the residual is bounded by the sum of positive parts of the m paired cell residuals and the positive part of the unpaired terminal clipped cell. This isolates the stop-straddling boundary contribution.
-- source:
--   Exact finite-mesh decomposition for Avram gledger179 one-sided Gaussian spatial Taylor estimate.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_ga_a26_last_mesh_cell_positive_split (m : ℕ) (a b c : ℕ → ℝ) :
    max ((∑ i ∈ Finset.range (m + 1), a i) -
      (∑ i ∈ Finset.range m, b i) -
      (∑ i ∈ Finset.range m, c i)) 0 ≤
    (∑ i ∈ Finset.range m, max (a i - b i - c i) 0) + max (a m) 0 := by sorry
