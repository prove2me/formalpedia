-- Prove2me | solution 1 for erdos_szekeres_asymmetric_graph_bound_of_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T11:58:00.623987+00:00
-- url     : https://prove2.me/submissions/49acd3bc-a60d-4072-ad38-3283e31f8244

import Mathlib
import Theorems.Thm_erdos_szekeres_asymmetric_graph_bound

theorem solution (k l n : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hn : Nat.choose (k + l - 2) (k - 1) ≤ n) :
    ∀ G : SimpleGraph (Fin n),
      (∃ s : Finset (Fin n), G.IsNClique k s) ∨
      (∃ s : Finset (Fin n), Gᶜ.IsNClique l s) := by
  intro G
  let f : Fin (Nat.choose (k + l - 2) (k - 1)) ↪ Fin n := Fin.castLEEmb hn
  let H : SimpleGraph (Fin (Nat.choose (k + l - 2) (k - 1))) := G.comap f
  rcases erdos_szekeres_asymmetric_graph_bound k l hk hl H with h | h
  · rcases h with ⟨s, hs⟩
    refine Or.inl ⟨s.image f, ?_⟩
    rw [SimpleGraph.isNClique_iff] at hs ⊢
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.isClique_iff]
      intro a ha b hb hab
      rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hb with ⟨y, hy, rfl⟩
      have hxy := hs.1 hx hy (fun he => hab (congrArg f he))
      simpa [H, SimpleGraph.comap_adj] using hxy
    · rw [Finset.card_image_of_injective _ f.injective]
      exact hs.2
  · rcases h with ⟨s, hs⟩
    refine Or.inr ⟨s.image f, ?_⟩
    rw [SimpleGraph.isNClique_iff] at hs ⊢
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.isClique_iff]
      intro a ha b hb hab
      rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hb with ⟨y, hy, rfl⟩
      have hxy := hs.1 hx hy (fun he => hab (congrArg f he))
      simpa [H, SimpleGraph.comap_adj] using hxy
    · rw [Finset.card_image_of_injective _ f.injective]
      exact hs.2
