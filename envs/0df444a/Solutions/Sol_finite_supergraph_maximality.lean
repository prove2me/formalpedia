-- Prove2me | solution 1 for finite_supergraph_maximality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:17:55.496861+00:00
-- url     : https://prove2.me/submissions/e3b8c3e0-f9f5-4c20-8178-b40ab590a58f

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop) (hG : P G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v⦄, G.Adj u v → H.Adj u v) ∧ P H ∧
      ∀ K : SimpleGraph V,
        (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) → P K → K = H := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter (fun K => G ≤ K ∧ P K)
  have hS : S.Nonempty := ⟨G, by simp [S, hG]⟩
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image S (fun K => K.edgeSet.ncard) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hH hmax
  refine ⟨H, fun u v h => hH.1 h, hH.2, ?_⟩
  intro K hHK' hK
  have hHK : H ≤ K := fun u v h => hHK' h
  have h1 := hmax K ⟨hH.1.trans hHK, hK⟩
  have heq : H.edgeSet = K.edgeSet :=
    Set.eq_of_subset_of_ncard_le (SimpleGraph.edgeSet_mono hHK) h1 (Set.toFinite _)
  exact (SimpleGraph.edgeSet_injective heq).symm
