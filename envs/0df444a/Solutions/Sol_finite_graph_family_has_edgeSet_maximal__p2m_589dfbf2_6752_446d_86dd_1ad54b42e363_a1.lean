-- Prove2me | solution 1 for finite_graph_family_has_edgeSet_maximal__p2m_589dfbf2_6752_446d_86dd_1ad54b42e363_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:33:51.157136+00:00
-- url     : https://prove2.me/submissions/8355ed3f-07bb-4348-8086-4893ba01faaa

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (hP : ∃ G, P G) :
    ∃ H : SimpleGraph V, P H ∧
      ∀ K : SimpleGraph V, P K → H.edgeSet ⊆ K.edgeSet →
        H.edgeSet = K.edgeSet := by
  classical
  obtain ⟨G, hG⟩ := hP
  let S : Set (SimpleGraph V) := {G | P G}
  obtain ⟨H, hH, hmax⟩ := S.toFinite.exists_maximal ⟨G, hG⟩
  refine ⟨H, hH, ?_⟩
  intro K hK hsub
  have hle : H ≤ K := SimpleGraph.edgeSet_subset_edgeSet.mp hsub
  have hback : K ≤ H := hmax hK hle
  have heq : H = K := le_antisymm hle hback
  simpa [heq]