-- Prove2me | solution 1 for mme_type2_ambient_isolated_induced_and_blocks_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:27:44.126395+00:00
-- url     : https://prove2.me/submissions/f190e1b7-6835-4f19-a218-8b5504c223b6

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
    (hisolated : ∀ e ∈ ambient,
      (∀ i : Fin 3, ∃ f ∈ kept, vertex i e = vertex i f) →
        e ∈ kept)
    (hmode : ∀ i : Fin 3,
      Function.Injective (fun e : kept ↦ vertex i e.1))
    (hblock : ∀ es : Fin 3 → kept,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ address (es i).1 i r) ≠ 0) →
      supportedMix (es 0).1 (es 1).1 (es 2).1) :
    (∀ x y z : kept,
      supportedMix x.1 y.1 z.1 → x = y ∧ y = z) ∧
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin kept.card ↦
        gradedAddressBlock G (address (kept.equivFin.symm j).1)))
      (T.kronPow N) := by
  classical
  have hinduced : ∀ x y z : kept,
      supportedMix x.1 y.1 z.1 → x = y ∧ y = z := by
    intro x y z hsupp
    obtain ⟨e, heAmbient, he0, he1, he2⟩ :=
      hclosure x.1 (hkept x.2) y.1 (hkept y.2) z.1 (hkept z.2) hsupp
    have heKept : e ∈ kept := hisolated e heAmbient (by
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
  refine ⟨hinduced, ?_⟩
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
    obtain ⟨h01, h12⟩ := hinduced (es 0) (es 1) (es 2) hsupp
    refine ⟨js 0, ?_⟩
    funext i
    fin_cases i
    · rfl
    · exact enum.injective h01.symm
    · exact enum.injective (h12.symm.trans h01.symm)
  simpa only [A, enum] using
    (mme_induced_graded_address_blocks_restrict G A hInduced)
