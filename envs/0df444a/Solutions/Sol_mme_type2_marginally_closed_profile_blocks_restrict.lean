-- Prove2me | solution 1 for mme_type2_marginally_closed_profile_blocks_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:17:35.946219+00:00
-- url     : https://prove2.me/submissions/fd292774-b22a-4bed-93e2-26dcf6b45bf4

import Mathlib
import Theorems.Thm_mme_induced_graded_address_blocks_restrict

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {Edge : Type*} {Vertex : Fin 3 → Type*}
    [DecidableEq Edge]
    {T : TensorObj K 3} {t N : ℕ}
    (G : T.TypeGrading t)
    (address : Edge → Fin 3 → Fin N → Fin t)
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (ambient target kept : Finset Edge)
    (hkept : kept ⊆ target)
    (hclosure : ∀ x ∈ target, ∀ y ∈ target, ∀ z ∈ target,
      supportedMix x y z →
        ∃ e ∈ ambient,
          vertex 0 e = vertex 0 x ∧
          vertex 1 e = vertex 1 y ∧
          vertex 2 e = vertex 2 z)
    (hprofile : ∀ e ∈ ambient,
      (∀ i : Fin 3, ∃ f ∈ target, vertex i e = vertex i f) →
        e ∈ target)
    (hisolated : ∀ e ∈ target,
      (∀ i : Fin 3, ∃ f ∈ kept, vertex i e = vertex i f) →
        e ∈ kept)
    (hmode : ∀ i : Fin 3,
      Function.Injective (fun e : kept ↦ vertex i e.1))
    (hblock : ∀ es : Fin 3 → kept,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ address (es i).1 i r) ≠ 0) →
      supportedMix (es 0).1 (es 1).1 (es 2).1) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin kept.card ↦
        gradedAddressBlock G (address (kept.equivFin.symm j).1)))
      (T.kronPow N) := by
  classical
  let enum : Fin kept.card ≃ kept := kept.equivFin.symm
  let A : Fin kept.card → Fin 3 → Fin N → Fin t :=
    fun j ↦ address (enum j).1
  have hInduced : ∀ js : Fin 3 → Fin kept.card,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ A (js i) i r) ≠ 0) →
      ∃ j : Fin kept.card, js = fun _ ↦ j := by
    intro js hnonzero
    let es : Fin 3 → kept := fun i ↦ enum (js i)
    have hsupp : supportedMix (es 0).1 (es 1).1 (es 2).1 :=
      hblock es (by
        intro r
        simpa only [A, es] using hnonzero r)
    obtain ⟨e, heAmbient, he0, he1, he2⟩ :=
      hclosure (es 0).1 (hkept (es 0).2)
        (es 1).1 (hkept (es 1).2)
        (es 2).1 (hkept (es 2).2) hsupp
    have heTarget : e ∈ target := hprofile e heAmbient (by
      intro i
      fin_cases i
      · exact ⟨(es 0).1, hkept (es 0).2, he0⟩
      · exact ⟨(es 1).1, hkept (es 1).2, he1⟩
      · exact ⟨(es 2).1, hkept (es 2).2, he2⟩)
    have heKept : e ∈ kept := hisolated e heTarget (by
      intro i
      fin_cases i
      · exact ⟨(es 0).1, (es 0).2, he0⟩
      · exact ⟨(es 1).1, (es 1).2, he1⟩
      · exact ⟨(es 2).1, (es 2).2, he2⟩)
    let e' : kept := ⟨e, heKept⟩
    have heq0 : e' = es 0 := hmode 0 he0
    have heq1 : e' = es 1 := hmode 1 he1
    have heq2 : e' = es 2 := hmode 2 he2
    refine ⟨js 0, ?_⟩
    funext i
    fin_cases i
    · rfl
    · exact enum.injective (heq1.symm.trans heq0)
    · exact enum.injective (heq2.symm.trans heq0)
  simpa only [A, enum] using
    (mme_induced_graded_address_blocks_restrict G A hInduced)
