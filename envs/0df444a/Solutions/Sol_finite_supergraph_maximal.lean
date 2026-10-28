-- Prove2me | solution 1 for finite_supergraph_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:51:03.048839+00:00
-- url     : https://prove2.me/submissions/2bba4a3b-8b10-4a34-b4c3-82d0cc0bed53

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P K) :
    ∃ K' : SimpleGraph V,
      K ≤ K' ∧ P K' ∧
        ∀ L : SimpleGraph V, K' ≤ L → P L → L ≤ K' := by
  classical
  let s : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => K ≤ G ∧ P G)
  have hs : s.Nonempty := by
    refine ⟨K, ?_⟩
    simp [s, hP]
  obtain ⟨K', hmax⟩ := s.exists_maximal hs
  have hmem : K' ∈ s := hmax.1
  have hK' : K ≤ K' := (Finset.mem_filter.mp hmem).2.1
  have hPK' : P K' := (Finset.mem_filter.mp hmem).2.2
  refine ⟨K', hK', hPK', ?_⟩
  intro L hK'L hPL
  have hKL : K ≤ L := hK'.trans hK'L
  have hmemL : L ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hKL, hPL⟩
  exact hmax.2 hmemL hK'L