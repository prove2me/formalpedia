-- Prove2me | solution 1 for finite_graph_property_maximal_supergraph_finite_max__p2m_98fc4204_1185_42f8_9d24_9b96a2776006_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:05:43.278871+00:00
-- url     : https://prove2.me/submissions/315a3c6b-3d77-49ba-ac49-ca1e63fa81b5

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hK : P K) :
    ∃ H : SimpleGraph V, ∃ dH : DecidableRel H.Adj,
      P H ∧
      (∀ u v, K.Adj u v → H.Adj u v) ∧
      (∀ (J : SimpleGraph V) (dJ : DecidableRel J.Adj),
        P J →
        (∀ u v, K.Adj u v → J.Adj u v) →
        (letI : DecidableRel H.Adj := dH
         letI : DecidableRel J.Adj := dJ
         J.edgeFinset.card ≤ H.edgeFinset.card)) := by
  classical
  letI : DecidableEq V := Classical.decEq V
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => P G ∧ ∀ u v, K.Adj u v → G.Adj u v
  have hS : S.Nonempty := by
    refine ⟨K, ?_⟩
    change K ∈ Finset.univ.filter (fun G => P G ∧ ∀ u v, K.Adj u v → G.Adj u v)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ K, hK, fun u v huv => huv⟩
  obtain ⟨H, hHmem, hHmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeFinset.card) hS
  have hHprops : P H ∧ ∀ u v, K.Adj u v → H.Adj u v := by
    change H ∈ Finset.univ.filter (fun G => P G ∧ ∀ u v, K.Adj u v → G.Adj u v) at hHmem
    exact (Finset.mem_filter.mp hHmem).2
  refine ⟨H, Classical.decRel H.Adj, hHprops.1, hHprops.2, ?_⟩
  intro J dJ hJ hJK
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  letI : DecidableRel J.Adj := dJ
  have hdec : dJ = Classical.decRel J.Adj := Subsingleton.elim _ _
  rw [hdec]
  have hJmem : J ∈ S := by
    change J ∈ Finset.univ.filter (fun G => P G ∧ ∀ u v, K.Adj u v → G.Adj u v)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ J, hJ, hJK⟩
  exact hHmax J hJmem
