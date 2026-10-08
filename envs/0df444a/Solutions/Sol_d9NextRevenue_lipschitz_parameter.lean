-- Prove2me | solution 1 for d9NextRevenue_lipschitz_parameter
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:29:11.082495+00:00
-- url     : https://prove2.me/submissions/6ea32bee-c375-45ca-9ffb-4aaab9fa8bc3

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9NextRevenue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (G : ℝ → ℝ → ℝ) (u v p x fare s L : ℝ)
    (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hG : ∀ t, 0 ≤ t → |G u t - G v t| ≤ L * |u - v|) :
    |d9NextRevenue (G u) p x fare s -
      d9NextRevenue (G v) p x fare s| ≤ L * |u - v| := by
  by_cases hprotection : s < p
  · simp only [d9NextRevenue, if_pos hprotection]
    exact hG s hs
  · by_cases hcapacity : s < p + x
    · simp only [d9NextRevenue, if_neg hprotection, if_pos hcapacity]
      have hbound := hG p hp
      convert hbound using 1 <;> ring
    · have hcap : p + x ≤ s := le_of_not_gt hcapacity
      have hres : 0 ≤ s - x := by linarith
      simp only [d9NextRevenue, if_neg hprotection, if_neg hcapacity]
      have hbound := hG (s - x) hres
      convert hbound using 1 <;> ring
