-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_finite_selected_cells_eventually_injective
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_finite_selected_cells_eventually_injective
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:30:27.978148+00:00
-- url     : https://prove2.me/theorems/cfc8e7f8-36a5-4b0a-be34-4d24c37ce007
-- title:
--   Finite original jump sets admit simultaneously distinct selected mesh cells
-- statement:
--   For each pair of distinct genuine jump times in a finite set, suppose their selected mesh indices are eventually distinct, as obtained from Hausdorff separation of shrinking cell endpoints. Show there exists one sufficiently fine grid level at which the index selection is injective across the entire finite set. The proof uses a finite intersection of eventual events and contains no jump-intensity or compensation assumption.

import Mathlib
open Filter Topology

theorem AvramDividend.Classical.avram_p2_a_zero_rate_finite_selected_cells_eventually_injective
    {α : Type*} (s : Finset α) (i : α → ℕ → ℕ)
    (h : ∀ u ∈ s, ∀ v ∈ s, u ≠ v →
      ∀ᶠ n : ℕ in atTop, i u n ≠ i v n) :
    ∀ᶠ n : ℕ in atTop, Set.InjOn (fun u => i u n) (s : Set α) := by sorry
