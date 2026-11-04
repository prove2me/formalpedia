-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_finite_grid_sum_eq_selected_injective_cells
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_finite_grid_sum_eq_selected_injective_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:41:41.21859+00:00
-- url     : https://prove2.me/theorems/f86701ef-e4c8-4ec2-89a1-5c8a267f3055
-- title:
--   Reindex a full supported finite grid sum by injectively selected actual jump cells
-- statement:
--   If all nonzero grid weights occur in the image of a finite injectively indexed set of actual jumps, the full grid sum equals the finite sum indexed by those jump times. This is the algebraic reduction needed for exact grid-to-jump convergence.

import Mathlib

namespace AvramDividend.Classical
end AvramDividend.Classical

open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_finite_grid_sum_eq_selected_injective_cells
    {α : Type*} [DecidableEq α]
    (S : Finset α) (n : ℕ) (j : α → ℕ)
    (hj : ∀ u ∈ S, j u < n + 1)
    (hinj : Set.InjOn j (↑S))
    (F : ℕ → ℝ)
    (hzero : ∀ i ∈ Finset.range (n + 1),
      i ∉ S.image j → F i = 0) :
    (∑ i ∈ Finset.range (n + 1), F i) =
      ∑ u ∈ S, F (j u) := by sorry
