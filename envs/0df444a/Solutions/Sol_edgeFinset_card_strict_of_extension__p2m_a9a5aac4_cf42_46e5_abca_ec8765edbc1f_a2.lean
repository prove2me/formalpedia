-- Prove2me | solution 1 for edgeFinset_card_strict_of_extension__p2m_a9a5aac4_cf42_46e5_abca_ec8765edbc1f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:24:40.13095+00:00
-- url     : https://prove2.me/submissions/69355248-9935-49fb-a050-caf48b4bb20a

import Mathlib
open SimpleGraph

theorem solution
    {V : Type} [Fintype V] (G H : SimpleGraph V)
    [Fintype {e // e ∈ G.edgeSet}] [Fintype {e // e ∈ H.edgeSet}]
    (u v : V) (hsub : G.edgeFinset ⊆ H.edgeFinset)
    (hAdj : H.Adj u v) (hwalk : ¬ Nonempty (G.Walk u v)) :
    G.edgeFinset.card < H.edgeFinset.card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · exact hsub
  · intro heq
    have hv : s(u, v) ∈ H.edgeFinset := by
      simpa using hAdj
    have hnot : s(u, v) ∉ G.edgeFinset := by
      intro hg
      have hadj : G.Adj u v := by
        simpa using hg
      exact hwalk ⟨hadj.toWalk⟩
    exact hnot (heq ▸ hv)