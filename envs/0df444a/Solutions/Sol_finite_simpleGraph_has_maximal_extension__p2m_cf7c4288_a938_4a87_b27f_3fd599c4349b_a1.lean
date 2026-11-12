-- Prove2me | solution 1 for finite_simpleGraph_has_maximal_extension__p2m_cf7c4288_a938_4a87_b27f_3fd599c4349b_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T13:46:51.084843+00:00
-- url     : https://prove2.me/submissions/afbac225-e2f6-4665-aaff-5ee5d624689d

import Mathlib

set_option autoImplicit false

/-- Every graph with a downward-closed property admits a maximal edge-supergraph with the property. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ ⦃G H : SimpleGraph V⦄, H.edgeSet ⊆ G.edgeSet → P G → P H)
    (H : SimpleGraph V) (hH : P H) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ P K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → P L →
        L.edgeSet ⊆ K.edgeSet := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun K : SimpleGraph V => H.edgeSet ⊆ K.edgeSet ∧ P K)
  have hS : S.Nonempty := ⟨H, by simp [S, hH]⟩
  obtain ⟨K, hKS, hmax⟩ :=
    Finset.exists_max_image S (fun K : SimpleGraph V => K.edgeSet.ncard) hS
  have hHsubK : H.edgeSet ⊆ K.edgeSet := (Finset.mem_filter.mp hKS).2.1
  have hPK : P K := (Finset.mem_filter.mp hKS).2.2
  refine ⟨K, hHsubK, hPK, ?_⟩
  intro L hKL hPL
  by_contra hLnot
  have hLmem : L ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hHsubK.trans hKL, hPL⟩
  have hle : L.edgeSet.ncard ≤ K.edgeSet.ncard := hmax L hLmem
  have hne : K.edgeSet ≠ L.edgeSet := by
    intro heq
    exact hLnot (heq ▸ le_refl L.edgeSet)
  have hssub : K.edgeSet ⊂ L.edgeSet := lt_of_le_of_ne hKL hne
  have hlt : K.edgeSet.ncard < L.edgeSet.ncard :=
    Set.ncard_lt_ncard hssub (Set.toFinite L.edgeSet)
  omega
