-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_finite_grid_sum_from_selected_cells
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_finite_grid_sum_from_selected_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:47:21.565581+00:00
-- url     : https://prove2.me/theorems/253a35ba-283a-4da6-841f-7a28a1261676
-- title:
--   Complete original mesh test sum converges from finitely selected genuine jump cells
-- statement:
--   For an abstract original mesh, the finitely many selected cells are eventually injective and always in the grid. Assume every non-selected cell eventually has zero compact-test weight. The full-grid sum is then exactly the selected-cell sum, which converges to the finite genuine jump-test sum by the already Proved P2-A finite continuous-sum theorem. No jump-rate assumption.

import Mathlib
open Filter Topology

theorem AvramDividend.Classical.avram_p2_a_zero_rate_finite_grid_sum_from_selected_cells
    {α : Type*} (s : Finset α)
    (grid : ℕ → Finset ℕ)
    (idx : α → ℕ → ℕ)
    (mark : ℕ → ℕ → ℝ) (jump : α → ℝ)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hinj : ∀ᶠ n : ℕ in atTop,
      Set.InjOn (fun u => idx u n) (s : Set α))
    (hinside : ∀ n, ∀ u ∈ s, idx u n ∈ grid n)
    (hzero : ∀ᶠ n : ℕ in atTop,
      ∀ j ∈ grid n, j ∉ s.image (fun u => idx u n) →
        f (mark n j) = 0)
    (hmark : ∀ u ∈ s,
      Tendsto (fun n => mark n (idx u n)) atTop (𝓝 (jump u))) :
    Tendsto (fun n => ∑ j ∈ grid n, f (mark n j))
      atTop (𝓝 (∑ u ∈ s, f (jump u)))  := by sorry
