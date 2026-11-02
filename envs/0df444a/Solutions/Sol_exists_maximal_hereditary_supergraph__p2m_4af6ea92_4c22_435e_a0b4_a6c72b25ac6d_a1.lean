-- Prove2me | solution 1 for exists_maximal_hereditary_supergraph__p2m_4af6ea92_4c22_435e_a0b4_a6c72b25ac6d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:43:04.622058+00:00
-- url     : https://prove2.me/submissions/26cf1fbf-f6ae-47ea-9c22-5fa0049e494a

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V -> Prop)
    (hhered : forall {G H : SimpleGraph V},
      (forall {u v : V}, H.Adj u v -> G.Adj u v) -> P G -> P H)
    (M : SimpleGraph V) (hM : P M) :
    Exists fun N : SimpleGraph V =>
      (forall {u v : V}, M.Adj u v -> N.Adj u v) /\
      P N /\
      (forall Q : SimpleGraph V,
        (forall {u v : V}, N.Adj u v -> Q.Adj u v) ->
        P Q -> Q = N) := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => M <= G /\ P G
  have hnonempty : admissible.Nonempty := by
    refine ⟨M, ?_⟩
    simp [admissible, hM]
  obtain ⟨N, hNmem, hNmax⟩ :=
    Finset.exists_max_image admissible (fun G => G.edgeFinset.card) hnonempty
  have hNprops : M <= N /\ P N := by
    simpa [admissible] using hNmem
  refine ⟨N, ?_, hNprops.2, ?_⟩
  · intro u v huv
    exact hNprops.1 huv
  · intro Q hNQ hQ
    have hNQle : N <= Q := fun u v huv => hNQ huv
    have hMQ : M <= Q := hNprops.1.trans hNQle
    have hQmem : Q ∈ admissible := by
      simp [admissible, hMQ, hQ]
    by_contra hne
    have hneq : N ≠ Q := fun h => hne h.symm
    have hstrict : N.edgeFinset ⊂ Q.edgeFinset := by
      rw [SimpleGraph.edgeFinset_ssubset_edgeFinset]
      exact ⟨hNQle, fun hQN => hneq (le_antisymm hNQle hQN)⟩
    have hcard : N.edgeFinset.card < Q.edgeFinset.card :=
      Finset.card_lt_card hstrict
    exact (not_lt_of_ge (hNmax Q hQmem)) hcard