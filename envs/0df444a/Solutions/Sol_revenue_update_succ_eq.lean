-- Prove2me | solution 1 for revenue_update_succ_eq
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:40:03.322937+00:00
-- url     : https://prove2.me/submissions/7b5a5288-a496-4520-80ad-28ff2ac77f58

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_update_of_gt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option autoImplicit false

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution
    (f p x : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) (y s : ℝ) :
    revenue f p (Function.update x (k + 1) y) (k + 1) s =
      if s < p k then revenue f p x k s
      else if s < p k + y then (s - p k) * f (k + 1) + revenue f p x k (p k)
      else y * f (k + 1) + revenue f p x k (s - y) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hR : ∀ t, revenue f p (Function.update x (j + 2) y) (j + 1) t = revenue f p x (j + 1) t :=
    fun t => revenue_update_of_gt f p x (j + 1) (j + 2) (by omega) y t
  have hy : Function.update x (j + 2) y (j + 2) = y := Function.update_self _ _ _
  show revenue f p (Function.update x (j + 2) y) (j + 2) s = _
  rw [revenue, hy, hR, hR, hR]
