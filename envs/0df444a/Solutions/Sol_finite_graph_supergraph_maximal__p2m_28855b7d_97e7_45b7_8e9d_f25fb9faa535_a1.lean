-- Prove2me | solution 1 for finite_graph_supergraph_maximal__p2m_28855b7d_97e7_45b7_8e9d_f25fb9faa535_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T19:18:27.919907+00:00
-- url     : https://prove2.me/submissions/7599294b-63f3-42f4-987c-3fe62ebe0e8f

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K) :
    ∃ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet ∧
      P L ∧
      ∀ M : SimpleGraph V,
        Set.Subset L.edgeSet M.edgeSet →
        P M →
        M.edgeSet = L.edgeSet := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => Set.Subset K.edgeSet G.edgeSet ∧ P G
  have hnonempty : admissible.Nonempty := by
    refine ⟨K, Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_univ K, Set.Subset.rfl, hK⟩
  obtain ⟨L, hLmem, hLmax⟩ :=
    Finset.exists_max_image admissible (fun G => G.edgeFinset.card) hnonempty
  have hLmem' : L ∈ admissible := hLmem
  have hLK : Set.Subset K.edgeSet L.edgeSet :=
    (Finset.mem_filter.mp hLmem').2.1
  have hLP : P L := (Finset.mem_filter.mp hLmem').2.2
  refine ⟨L, hLK, hLP, ?_⟩
  intro M hLM hMP
  have hMmem : M ∈ admissible := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ M, ?_⟩
    exact ⟨Set.Subset.trans hLK hLM, hMP⟩
  have hcard : M.edgeFinset.card ≤ L.edgeFinset.card := hLmax M hMmem
  have hsub : L.edgeFinset ⊆ M.edgeFinset := by
    intro e he
    have he' : e ∈ L.edgeSet := by simpa using he
    have he'' : e ∈ M.edgeSet := hLM he'
    simpa using he''
  have hcard' : L.edgeFinset.card ≤ M.edgeFinset.card :=
    Finset.card_le_card hsub
  have hcardEq : L.edgeFinset.card = M.edgeFinset.card :=
    Nat.le_antisymm hcard' hcard
  have hfinEq : L.edgeFinset = M.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub (Nat.le_of_eq hcardEq.symm)
  have hedge : L.edgeSet = M.edgeSet := by
    ext e
    have := Finset.ext_iff.mp hfinEq e
    simpa using this
  exact hedge.symm
