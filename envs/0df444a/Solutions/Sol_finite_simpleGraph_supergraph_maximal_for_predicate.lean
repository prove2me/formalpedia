-- Prove2me | solution 1 for finite_simpleGraph_supergraph_maximal_for_predicate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:14:49.035543+00:00
-- url     : https://prove2.me/submissions/8b4f0dec-8981-4d0a-8774-3609aef4315a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
      (∀ K : SimpleGraph V, H ≤ K → P K → K = H) := by
  classical
  let s : Set (SimpleGraph V) := {H | G ≤ H ∧ P H}
  have hG : G ∈ s := ⟨le_rfl, hP⟩
  obtain ⟨H, hHs, hmax⟩ := (Set.toFinite s).exists_maximal ⟨G, hG⟩
  refine ⟨H, hHs.1, hHs.2, ?_⟩
  intro K hHK hPK
  have hKs : K ∈ s := ⟨hHs.1.trans hHK, hPK⟩
  have hKH : K ≤ H := hmax hKs hHK
  exact le_antisymm hKH hHK