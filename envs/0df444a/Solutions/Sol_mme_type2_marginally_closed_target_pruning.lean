-- Prove2me | solution 1 for mme_type2_marginally_closed_target_pruning
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:26:34.677767+00:00
-- url     : https://prove2.me/submissions/b10ad9a4-eba6-4678-b997-f895030d4bfa

import Mathlib
import Theorems.Thm_mme_tripartite_target_isolation_pruning

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Edge : Type*} {Vertex : Fin 3 → Type*}
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (ambient target : Finset Edge)
    (hclosure : ∀ x ∈ target, ∀ y ∈ target, ∀ z ∈ target,
      supportedMix x y z →
        ∃ e ∈ ambient,
          vertex 0 e = vertex 0 x ∧
          vertex 1 e = vertex 1 y ∧
          vertex 2 e = vertex 2 z)
    (hprofile : ∀ e ∈ ambient,
      (∀ i : Fin 3, ∃ f ∈ target, vertex i e = vertex i f) →
        e ∈ target) :
    let collisions := (target ×ˢ target).filter (fun p ↦
      p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)
    ∃ kept : Finset Edge,
      kept ⊆ target ∧
      (∀ i : Fin 3,
        Function.Injective (fun e : kept ↦ vertex i e.1)) ∧
      (∀ x y z : kept,
        supportedMix x.1 y.1 z.1 → x = y ∧ y = z) ∧
      target.card ≤ kept.card + collisions.card := by
  classical
  dsimp only
  obtain ⟨kept, hkept, hseparated, hisolated, hcard⟩ :=
    mme_tripartite_target_isolation_pruning
      vertex target target (by exact fun _ h ↦ h)
  have hmode : ∀ i : Fin 3,
      Function.Injective (fun e : kept ↦ vertex i e.1) := by
    intro i x y hxy
    apply Subtype.ext
    by_contra hne
    exact hseparated x.1 x.2 y.1 y.2 hne i hxy
  refine ⟨kept, hkept, hmode, ?_, hcard⟩
  intro x y z hsupp
  obtain ⟨e, heAmbient, he0, he1, he2⟩ :=
    hclosure x.1 (hkept x.2) y.1 (hkept y.2) z.1 (hkept z.2) hsupp
  have heTarget : e ∈ target := hprofile e heAmbient (by
    intro i
    fin_cases i
    · exact ⟨x.1, hkept x.2, he0⟩
    · exact ⟨y.1, hkept y.2, he1⟩
    · exact ⟨z.1, hkept z.2, he2⟩)
  have heKept : e ∈ kept := hisolated e heTarget (by
    intro i
    fin_cases i
    · exact ⟨x.1, x.2, he0⟩
    · exact ⟨y.1, y.2, he1⟩
    · exact ⟨z.1, z.2, he2⟩)
  let e' : kept := ⟨e, heKept⟩
  have hex : e' = x := hmode 0 he0
  have hey : e' = y := hmode 1 he1
  have hez : e' = z := hmode 2 he2
  exact ⟨hex.symm.trans hey, hey.symm.trans hez⟩
