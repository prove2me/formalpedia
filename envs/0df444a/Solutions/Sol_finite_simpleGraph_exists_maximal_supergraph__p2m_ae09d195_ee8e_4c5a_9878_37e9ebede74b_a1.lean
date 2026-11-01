-- Prove2me | solution 1 for finite_simpleGraph_exists_maximal_supergraph__p2m_ae09d195_ee8e_4c5a_9878_37e9ebede74b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:22:36.084091+00:00
-- url     : https://prove2.me/submissions/5145385c-3cef-44d8-b5e1-0e0bab8668cc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : P G) :
    ∃ (T : SimpleGraph V) (dT : DecidableRel T.Adj),
      P T ∧
      (letI : DecidableRel G.Adj := dG
       letI : DecidableRel T.Adj := dT
       G.edgeFinset ⊆ T.edgeFinset) ∧
      (∀ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
        P U →
        (letI : DecidableRel T.Adj := dT
         letI : DecidableRel U.Adj := dU
         T.edgeFinset ⊆ U.edgeFinset) →
        T = U) := by
  classical
  let S : Set (SimpleGraph V) := {H | P H ∧ G ≤ H}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := by
    exact ⟨G, by simp [S, hG]⟩
  let f : SimpleGraph V → Nat := fun H => H.edgeSet.ncard
  obtain ⟨T, hTS, hmax⟩ := Set.exists_max_image S f hSfinite hSnonempty
  let dT : DecidableRel T.Adj := Classical.decRel _
  letI : DecidableRel G.Adj := dG
  letI : DecidableRel T.Adj := dT
  have hGT : G.edgeFinset ⊆ T.edgeFinset := by
    simpa only [SimpleGraph.edgeFinset_subset_edgeFinset] using hTS.2
  refine ⟨T, dT, hTS.1, hGT, ?_⟩
  intro U dU hU hTU
  have hTU_order : T ≤ U := by
    simpa only [SimpleGraph.edgeFinset_subset_edgeFinset] using hTU
  have hGU : G ≤ U := le_trans hTS.2 hTU_order
  have hUS : U ∈ S := ⟨hU, hGU⟩
  have hmax' := hmax U hUS
  have hcard : U.edgeFinset.card ≤ T.edgeFinset.card := by
    simpa only [f, SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using hmax'
  have hTU' : T.edgeFinset ⊆ U.edgeFinset := by
    simpa only [SimpleGraph.edgeFinset_subset_edgeFinset] using hTU_order
  apply SimpleGraph.edgeFinset_inj.mp
  exact Finset.eq_of_subset_of_card_le hTU' hcard