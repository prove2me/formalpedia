-- Prove2me | solution 2 for finite_edge_insertion_closure__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:51:37.572986+00:00
-- url     : https://prove2.me/submissions/6f091798-fc31-48af-967a-5fee94cdfd9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Definitions.Def_EdgeInsertionReachable__p2m_313288c9_76e4_493b_841a_755972300fa5_a3
import Theorems.Thm_finite_subgraph_edge_insertion_reachable__p2m_313288c9_76e4_493b_841a_755972300fa5_a3

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (Q : SimpleGraph V → Prop)
    (hbase : Q ⊥)
    (hstep : ∀ (K : SimpleGraph V), K ≤ G →
      ∀ u v : V, u < v → G.Adj u v → ¬ K.Adj u v →
      Q K → Q (K ⊔ SimpleGraph.edge u v)) :
    ∀ H : SimpleGraph V, H ≤ G → Q H := by
  intro H hHG
  have hreach :=
    finite_subgraph_edge_insertion_reachable__p2m_313288c9_76e4_493b_841a_755972300fa5_a3
      G H hHG
  induction hreach with
  | empty => exact hbase
  | @insert K u v hprev hK hGuv hnot ih =>
      rcases lt_or_gt_of_ne hGuv.ne with huv | hvu
      · exact hstep K hK u v huv hGuv hnot (ih hK)
      · have hGvu : G.Adj v u := hGuv.symm
        have hnotvu : ¬ K.Adj v u := fun h => hnot h.symm
        simpa [SimpleGraph.edge_comm] using
          (hstep K hK v u hvu hGvu hnotvu (ih hK))