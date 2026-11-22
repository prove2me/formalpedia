-- Prove2me | solution 1 for nonempty_hom_of_forall_finite_subgraph_hom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:38:27.01355+00:00
-- url     : https://prove2.me/submissions/bc0be07a-ac5d-45d6-8400-475bed0b739c

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.Compactness
import Definitions.Def_Polychromatic_Compactness

set_option autoImplicit true

theorem _root_.solution {V W : Type*} [Finite W]
    {G : SimpleGraph V} {F : SimpleGraph W}
    (h : ∀ G' : G.Subgraph, G'.verts.Finite → G'.coe →g F) : Nonempty (G →g F) := by
  have := G.toSubgraph
  let g : (s : Set V) → s.Finite → s → W := fun s hs ↦ h (SimpleGraph.Subgraph.induce ⊤ s) hs
  obtain ⟨χ, hχ⟩ := Set.Finite.rado_selection_subtype (β := fun _ ↦ W) g
  refine ⟨⟨χ, ?_⟩⟩
  intro a b hab
  let a' : (G.subgraphOfAdj hab).verts := ⟨a, by simp⟩
  let b' : (G.subgraphOfAdj hab).verts := ⟨b, by simp⟩
  have hab' : (G.subgraphOfAdj hab).Adj a' b' := by simp [a', b']
  change F.Adj (χ a') (χ b')
  obtain ⟨H, hHfin, hHsub, hHeq⟩ := hχ (G.subgraphOfAdj hab).verts (by simp)
  rw [hHeq, hHeq]
  simp only [g]
  apply (h ((⊤ : G.Subgraph).induce H) hHfin).map_adj
  simp only [SimpleGraph.subgraphOfAdj_verts, Set.insert_subset_iff,
    Set.singleton_subset_iff] at hHsub
  exact ⟨hHsub.1, hHsub.2, hab⟩
