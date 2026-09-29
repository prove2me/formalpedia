-- Prove2me | solution 1 for mme_tripartite_target_isolation_pruning
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:08:16.168515+00:00
-- url     : https://prove2.me/submissions/6a689c95-606a-4a66-83f9-b025123b65f2

import Mathlib.Data.Finset.Prod

set_option autoImplicit false

/-- Delete precisely those target edges which collide with any edge of the
ambient hypergraph.  The surviving target edges form a matching which is
vertex-induced relative to the whole ambient edge set. -/
theorem solution
    {Edge : Type*} {Vertex : Fin 3 → Type*}
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (v : ∀ i, Edge → Vertex i) (E T : Finset Edge) (hTE : T ⊆ E) :
    let C := (T ×ˢ E).filter (fun p =>
      p.1 ≠ p.2 ∧ ∃ i : Fin 3, v i p.1 = v i p.2)
    ∃ F : Finset Edge,
      F ⊆ T ∧
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y →
        ∀ i : Fin 3, v i x ≠ v i y) ∧
      (∀ e ∈ E,
        (∀ i : Fin 3, ∃ f ∈ F, v i e = v i f) → e ∈ F) ∧
      T.card ≤ F.card + C.card := by
  classical
  dsimp only
  let C : Finset (Edge × Edge) := (T ×ˢ E).filter (fun p =>
    p.1 ≠ p.2 ∧ ∃ i : Fin 3, v i p.1 = v i p.2)
  let bad : Finset Edge := C.image Prod.fst
  let F : Finset Edge := T \ bad
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · exact Finset.sdiff_subset
  · intro x hx y hy hxy i hvi
    have hxT : x ∈ T := Finset.sdiff_subset hx
    have hyE : y ∈ E := hTE (Finset.sdiff_subset hy)
    have hpair : (x, y) ∈ C := by
      simp only [C, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hxT, hyE⟩, hxy, ⟨i, hvi⟩⟩
    have hxbad : x ∈ bad :=
      Finset.mem_image.mpr ⟨(x, y), hpair, rfl⟩
    exact (Finset.mem_sdiff.mp hx).2 hxbad
  · intro e heE hvertices
    obtain ⟨f, hfF, hef⟩ := hvertices (0 : Fin 3)
    by_cases hfe : f = e
    · simpa only [hfe] using hfF
    · have hfT : f ∈ T := Finset.sdiff_subset hfF
      have hpair : (f, e) ∈ C := by
        simp only [C, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hfT, heE⟩, hfe, ⟨(0 : Fin 3), hef.symm⟩⟩
      have hfbad : f ∈ bad :=
        Finset.mem_image.mpr ⟨(f, e), hpair, rfl⟩
      exact False.elim ((Finset.mem_sdiff.mp hfF).2 hfbad)
  · have hbadT : bad ⊆ T := by
      intro x hx
      obtain ⟨p, hpC, rfl⟩ := Finset.mem_image.mp hx
      have hpC' : p ∈ (T ×ˢ E).filter (fun p =>
          p.1 ≠ p.2 ∧ ∃ i : Fin 3, v i p.1 = v i p.2) := by
        simpa only [C] using hpC
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hpC').1).1
    have hcard : F.card + bad.card = T.card := by
      simpa only [F] using Finset.card_sdiff_add_card_eq_card hbadT
    have hbadC : bad.card ≤ C.card := Finset.card_image_le
    have hCle : C.card ≤
        ((T ×ˢ E).filter (fun p =>
          p.1 ≠ p.2 ∧ ∃ i : Fin 3, v i p.1 = v i p.2)).card := by
      change C.card ≤ C.card
      exact le_rfl
    omega
