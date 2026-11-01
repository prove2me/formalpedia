-- Prove2me | solution 1 for exists_maximal_planar_supergraph__p2m_10eaf2f1_7409_4fae_95fa_e1e70a835601_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:08:10.084346+00:00
-- url     : https://prove2.me/submissions/4300c33e-93a0-4d81-9d38-e114806dd5a5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      G ≤ M ∧
      ∀ (N : SimpleGraph V),
        M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by
  classical
  let S : Type := {H : SimpleGraph V // G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H}
  have hSfinite : Finite S := by
    let edgeMap : S → Finset (Sym2 V) := fun H => by
      letI : Fintype H.1.edgeSet := Fintype.ofFinite _
      exact H.1.edgeFinset
    have edgeMap_injective : Function.Injective edgeMap := by
      intro H K h
      apply Subtype.ext
      letI : Fintype H.1.edgeSet := Fintype.ofFinite _
      letI : Fintype K.1.edgeSet := Fintype.ofFinite _
      exact SimpleGraph.edgeFinset_inj.mp h
    exact Finite.of_injective edgeMap edgeMap_injective
  letI : Finite S := hSfinite
  have hSne : (Set.univ : Set S).Nonempty :=
    ⟨⟨G, le_rfl, hG⟩, Set.mem_univ _⟩
  obtain ⟨M, hM⟩ :=
    (Set.finite_univ : (Set.univ : Set S).Finite).exists_maximal hSne
  have hMmax : ∀ ⦃N : S⦄, M ≤ N → N ≤ M := by
    intro N hMN
    exact hM.2 (Set.mem_univ N) hMN
  refine ⟨M.1, inferInstance, M.2.2, M.2.1, ?_⟩
  intro N hMN hN
  let N' : S := ⟨N, ⟨M.2.1.trans hMN, hN⟩⟩
  exact hMmax (N := N') hMN