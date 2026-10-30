-- Prove2me | solution 1 for finite_edge_insertion_closure__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T23:51:23.400442+00:00
-- url     : https://prove2.me/submissions/00ca9ff0-0cfc-465f-ade6-29fc80dafda7

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (Q : SimpleGraph V → Prop)
    (hbase : Q ⊥)
    (hstep : ∀ (K : SimpleGraph V), K ≤ G →
      ∀ u v : V, u < v → G.Adj u v → ¬ K.Adj u v →
      Q K → Q (K ⊔ SimpleGraph.edge u v)) :
    ∀ H : SimpleGraph V, H ≤ G → Q H := by
  classical
  have aux : ∀ s : Finset (Sym2 V), (↑s : Set (Sym2 V)) ⊆ G.edgeSet →
      Q (SimpleGraph.fromEdgeSet (↑s : Set (Sym2 V))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro hs
      simpa only [Finset.coe_empty, SimpleGraph.fromEdgeSet_empty] using hbase
    | @insert e s he ih =>
      intro hs
      have heG : e ∈ G.edgeSet := hs (by simp)
      have hsG : (↑s : Set (Sym2 V)) ⊆ G.edgeSet := by
        intro x hx
        exact hs (by simp [hx])
      have hK : SimpleGraph.fromEdgeSet (↑s : Set (Sym2 V)) ≤ G := by
        apply SimpleGraph.le_iff_adj.mpr
        intro x y hxy
        exact G.mem_edgeSet.mp (hsG (((SimpleGraph.fromEdgeSet_adj (↑s : Set (Sym2 V))).mp hxy).1))
      obtain ⟨⟨u, v⟩, rfl⟩ := Sym2.mk_surjective e
      dsimp only [Function.uncurry_apply_pair] at he hs heG ⊢
      have huv : G.Adj u v := G.mem_edgeSet.mp heG
      have hneq : u ≠ v := huv.ne
      have hnot : ¬ (SimpleGraph.fromEdgeSet (↑s : Set (Sym2 V))).Adj u v := by
        simp only [SimpleGraph.fromEdgeSet_adj, Finset.mem_coe]
        exact fun h ↦ he h.1
      have heq : SimpleGraph.fromEdgeSet (↑(insert s(u, v) s) : Set (Sym2 V)) =
          SimpleGraph.fromEdgeSet (↑s : Set (Sym2 V)) ⊔ SimpleGraph.edge u v := by
        rw [Finset.coe_insert, Set.insert_eq, SimpleGraph.fromEdgeSet_union,
          SimpleGraph.edge, sup_comm]
      rw [heq]
      rcases lt_or_gt_of_ne hneq with hlt | hlt
      · exact hstep _ hK u v hlt huv hnot (ih hsG)
      · have hnot' : ¬ (SimpleGraph.fromEdgeSet (↑s : Set (Sym2 V))).Adj v u :=
          fun h ↦ hnot h.symm
        simpa only [SimpleGraph.edge_comm] using hstep _ hK v u hlt huv.symm hnot' (ih hsG)
  intro H hHG
  have hsubset : (↑H.edgeFinset : Set (Sym2 V)) ⊆ G.edgeSet := by
    simpa only [SimpleGraph.coe_edgeFinset, SimpleGraph.edgeSet_subset_edgeSet] using hHG
  simpa only [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet] using aux H.edgeFinset hsubset

