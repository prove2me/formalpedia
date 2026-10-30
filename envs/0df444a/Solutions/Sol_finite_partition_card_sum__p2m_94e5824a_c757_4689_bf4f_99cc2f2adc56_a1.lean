-- Prove2me | solution 1 for finite_partition_card_sum__p2m_94e5824a_c757_4689_bf4f_99cc2f2adc56_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:31:51.552493+00:00
-- url     : https://prove2.me/submissions/7b7be64e-ceb8-469e-8237-8e30599e38a2

import Mathlib

theorem solution
    {V : Type} [Fintype V] (parts : Finset (Finset V))
    (huniq : ∀ v : V, ∃! W : Finset V, W ∈ parts ∧ v ∈ W) :
    Fintype.card V = ∑ W ∈ parts, W.card := by
  classical
  have hdisj : (parts : Set (Finset V)).PairwiseDisjoint
      (fun W : Finset V => W) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro A hA B hB hab
    obtain ⟨v, hv⟩ := Finset.Nonempty.exists_mem hab
    have hvA : v ∈ A := (Finset.mem_inter.mp hv).1
    have hvB : v ∈ B := (Finset.mem_inter.mp hv).2
    obtain ⟨W, hW, hWuniq⟩ := huniq v
    have hAW : A = W := hWuniq A ⟨hA, hvA⟩
    have hBW : B = W := hWuniq B ⟨hB, hvB⟩
    exact hAW.trans hBW.symm
  have hcover : parts.biUnion (fun W : Finset V => W) = Finset.univ := by
    ext v
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨W, hWp, hvW⟩
      exact Finset.mem_univ v
    · intro _
      obtain ⟨W, hW, _⟩ := huniq v
      exact ⟨W, hW.1, hW.2⟩
  calc
    Fintype.card V = (Finset.univ : Finset V).card := by simp
    _ = (parts.biUnion (fun W : Finset V => W)).card := by rw [← hcover]
    _ = ∑ W ∈ parts, W.card := by
      simpa using (Finset.card_biUnion (s := parts)
        (t := fun W : Finset V => W) hdisj)