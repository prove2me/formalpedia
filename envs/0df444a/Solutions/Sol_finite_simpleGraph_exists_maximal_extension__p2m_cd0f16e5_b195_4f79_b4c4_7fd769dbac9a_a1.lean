-- Prove2me | solution 1 for finite_simpleGraph_exists_maximal_extension__p2m_cd0f16e5_b195_4f79_b4c4_7fd769dbac9a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:55:32.069076+00:00
-- url     : https://prove2.me/submissions/5da28865-68ac-40dc-b195-aaaa1fa9df34

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (M : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hmono : ∀ {A B : SimpleGraph V}, B.edgeSet ⊆ A.edgeSet → P A → P B)
    (hM : P M) :
    ∃ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet ∧ P N ∧
      ∀ Q : SimpleGraph V, N.edgeSet ⊆ Q.edgeSet → P Q → Q.edgeSet = N.edgeSet := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter fun G =>
    M.edgeSet ⊆ G.edgeSet ∧ P G
  have hS : S.Nonempty := by
    refine ⟨M, ?_⟩
    simp [S, hM]
  obtain ⟨N, hNS, hmax⟩ := Finset.exists_max_image S (fun G => G.edgeSet.ncard) hS
  have hN : M.edgeSet ⊆ N.edgeSet ∧ P N := by
    simpa [S] using hNS
  refine ⟨N, hN.1, hN.2, ?_⟩
  intro Q hNQ hPQ
  have hQS : Q ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hN.1.trans hNQ, hPQ⟩
  by_contra hne
  have hne' : N.edgeSet ≠ Q.edgeSet := by
    intro he
    apply hne
    exact he.symm
  have hproper : N.edgeSet ⊂ Q.edgeSet :=
    Set.ssubset_iff_subset_ne.mpr ⟨hNQ, hne'⟩
  have hlt : N.edgeSet.ncard < Q.edgeSet.ncard := Set.ncard_lt_ncard hproper
  exact (not_le_of_gt hlt) (hmax Q hQS)