-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_right_closed_grid_cell_locator_unique
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_right_closed_grid_cell_locator_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:45:12.081597+00:00
-- url     : https://prove2.me/theorems/35821f1a-f3fd-4821-8025-43657ef15ab9
-- title:
--   Every positive time is in at most one right-closed uniform cell
-- statement:
--   Prove disjointness of uniform half-open right-closed cells for a nonnegative step. A time strictly above both left endpoints and at most both right endpoints forces integer indices to agree, including the exact-endpoint convention.

import Mathlib

namespace AvramDividend.Classical
end AvramDividend.Classical

open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_right_closed_grid_cell_locator_unique
    (δ u : ℝ≥0) (i j : ℕ)
    (hiL : (i : ℝ≥0) * δ < u)
    (hiR : u ≤ ((i + 1 : ℕ) : ℝ≥0) * δ)
    (hjL : (j : ℝ≥0) * δ < u)
    (hjR : u ≤ ((j + 1 : ℕ) : ℝ≥0) * δ) :
    i = j := by sorry
