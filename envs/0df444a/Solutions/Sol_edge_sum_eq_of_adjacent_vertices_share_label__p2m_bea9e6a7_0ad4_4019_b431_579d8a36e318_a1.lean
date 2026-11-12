-- Prove2me | solution 1 for edge_sum_eq_of_adjacent_vertices_share_label__p2m_bea9e6a7_0ad4_4019_b431_579d8a36e318_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T13:42:16.021728+00:00
-- url     : https://prove2.me/submissions/b348d425-11c5-493d-93de-9dfb896421a8

import Mathlib

open scoped BigOperators

set_option autoImplicit false

/-- If adjacent vertices always share a label, the edge counts of the induced subgraphs on the
label fibres sum to the total edge count. -/
theorem solution {V ι : Type} [Fintype V] [Fintype ι] (G : SimpleGraph V) (label : V → ι)
    (h : ∀ ⦃u v : V⦄, G.Adj u v → label u = label v) :
    (Finset.univ.sum fun i : ι => (G.induce {v : V | label v = i}).edgeSet.ncard) =
      G.edgeSet.ncard := by
  classical
  set B : ι → Finset (Sym2 V) :=
    fun i => G.edgeFinset ∩ (Finset.univ.filter (fun v : V => label v = i)).sym2 with hB
  have hterm : ∀ i : ι, (G.induce {v : V | label v = i}).edgeSet.ncard = (B i).card := by
    intro i
    rw [Set.ncard_eq_toFinset_card']
    change (G.induce {v : V | label v = i}).edgeFinset.card = (B i).card
    rw [← Finset.card_map (f := (Function.Embedding.subtype (· ∈ {v : V | label v = i})).sym2Map)]
    rw [SimpleGraph.map_edgeFinset_induce (s := {v : V | label v = i}) (G := G)]
    simp only [hB, Set.toFinset_ofPred]
  have hnonempty : ∀ e : Sym2 V, e.toFinset.Nonempty := by
    intro e
    induction e using Sym2.ind with
    | _ u v => exact ⟨u, by simp⟩
  have hcover : Finset.univ.biUnion B = G.edgeFinset := by
    ext e
    constructor
    · intro he
      rw [Finset.mem_biUnion] at he
      obtain ⟨i, -, hi⟩ := he
      exact (Finset.mem_inter.mp hi).1
    · intro he
      revert he
      induction e using Sym2.ind with
      | _ u v =>
        intro he
        have h1 : s(u, v) ∈ G.edgeSet := by simpa [SimpleGraph.edgeFinset] using he
        have hadj : G.Adj u v := (SimpleGraph.mem_edgeSet G).mp h1
        refine Finset.mem_biUnion.mpr ⟨label u, Finset.mem_univ _, ?_⟩
        simp only [hB, Finset.mem_inter]
        refine ⟨he, ?_⟩
        rw [Finset.mem_sym2_iff]
        intro a ha
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ a, ?_⟩
        rcases Sym2.mem_iff.mp ha with rfl | rfl
        · rfl
        · exact (h hadj).symm
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint B := by
    intro i _ j _ hij
    change Disjoint (B i) (B j)
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [hB, Finset.mem_inter] at he he'
    rw [Finset.mem_sym2_iff] at he he'
    obtain ⟨a, ha⟩ := hnonempty e
    have ha' : a ∈ e := by rwa [Sym2.mem_toFinset] at ha
    have hia : label a = i := by simpa using (he.2 a ha')
    have hja : label a = j := by simpa using (he'.2 a ha')
    exact hij (hia.symm.trans hja)
  have hcard : G.edgeFinset.card = ∑ i : ι, (B i).card := by
    rw [← hcover, Finset.card_biUnion hdisj]
  calc (Finset.univ.sum fun i : ι => (G.induce {v : V | label v = i}).edgeSet.ncard)
      = ∑ i : ι, (B i).card := Finset.sum_congr rfl (fun i _ => hterm i)
    _ = G.edgeFinset.card := hcard.symm
    _ = G.edgeSet.ncard := by
        rw [Set.ncard_eq_toFinset_card']
        rfl
