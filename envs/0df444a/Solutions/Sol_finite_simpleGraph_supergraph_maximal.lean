-- Prove2me | solution 1 for finite_simpleGraph_supergraph_maximal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:31.382771+00:00
-- url     : https://prove2.me/submissions/d39ecc77-6ab8-4e1c-8955-58db99ab2a95

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
        (∀ K : SimpleGraph V, P K → H ≤ K → K = H) := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ P J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun L hPL hL =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hL, hPL⟩ hL) hL⟩
