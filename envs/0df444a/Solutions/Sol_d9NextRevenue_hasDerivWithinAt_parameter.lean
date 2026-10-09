-- Prove2me | solution 1 for d9NextRevenue_hasDerivWithinAt_parameter
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T14:44:46.921204+00:00
-- url     : https://prove2.me/submissions/1e5025f2-d32a-4275-9a97-81539bff3b3b

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9NextRevenue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (G : ℝ → ℝ → ℝ) (D : ℝ → ℝ) (p x fare s u : ℝ)
    (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hG : ∀ t, 0 ≤ t →
      HasDerivWithinAt (fun v => G v t) (D t) (Set.Ici u) u) :
    HasDerivWithinAt (fun v => d9NextRevenue (G v) p x fare s)
      (if s < p then D s else if s < p + x then D p else D (s - x))
      (Set.Ici u) u := by
  by_cases hprotection : s < p
  · simpa [d9NextRevenue, hprotection] using hG s hs
  · by_cases hcapacity : s < p + x
    · have hsum := (hG p hp).const_add ((s - p) * fare)
      simpa [d9NextRevenue, hprotection, hcapacity] using hsum
    · have hcap : p + x ≤ s := le_of_not_gt hcapacity
      have hresidual : 0 ≤ s - x := by linarith
      simp only [d9NextRevenue, if_neg hprotection, if_neg hcapacity]
      have hsum := (hG (s - x) hresidual).const_add (x * fare)
      simpa [d9NextRevenue, hprotection, hcapacity] using hsum
