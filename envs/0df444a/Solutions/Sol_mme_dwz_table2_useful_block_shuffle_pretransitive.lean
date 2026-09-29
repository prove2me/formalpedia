-- Prove2me | solution 1 for mme_dwz_table2_useful_block_shuffle_pretransitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T07:49:21.858757+00:00
-- url     : https://prove2.me/submissions/76e1e60c-352d-42cf-b8cd-9f313ee73764

import Definitions.Def_mme_dwz_table2_useful_block_shuffle_action
import Mathlib.GroupTheory.GroupAction.Transitive

set_option autoImplicit false
set_option warningAsError true

open MME.DWZTable2StandardForm

universe u

theorem solution
    (m : ℕ) {Position : Type u} [Fintype Position]
    (outer : Position → Fin 15) :
    MulAction.IsPretransitive
      (UsefulBlockShuffleGroup outer) (UsefulBlock m outer) := by
  have fine_pair_eq : ∀ (x p : Fin 3 × Fin 3),
      x.1 = p.1 →
      MME.DWZTable2Counts.coarseOf x =
        MME.DWZTable2Counts.coarseOf p → x = p := by
    intro x p hfst hcoarse
    apply Prod.ext
    · exact hfst
    · apply Fin.ext
      have hsum := congrArg Fin.val hcoarse
      simp only [MME.DWZTable2Counts.coarseOf] at hsum
      have hfstval := congrArg Fin.val hfst
      omega
  constructor
  intro small₁ small₂
  let cell₁ : Position → Fin 15 × Fin 3 :=
    fun t ↦ (outer t, (small₁.1 t).1)
  let cell₂ : Position → Fin 15 × Fin 3 :=
    fun t ↦ (outer t, (small₂.1 t).1)
  have hcard : ∀ c : Fin 15 × Fin 3,
      Fintype.card {t : Position // cell₁ t = c} =
        Fintype.card {t : Position // cell₂ t = c} := by
    rintro ⟨s, a⟩
    simpa only [cell₁, cell₂, Prod.mk.injEq] using
      (small₁.2.2 s a).trans (small₂.2.2 s a).symm
  let fiberEquiv : ∀ c : Fin 15 × Fin 3,
      {t : Position // cell₁ t = c} ≃
        {t : Position // cell₂ t = c} :=
    fun c ↦ Fintype.equivOfCardEq (hcard c)
  let e : Position ≃ Position := Equiv.ofFiberEquiv fiberEquiv
  have hcell : ∀ t, cell₂ (e t) = cell₁ t :=
    Equiv.ofFiberEquiv_map fiberEquiv
  have houter : ∀ t, outer (e t) = outer t := by
    intro t
    exact congrArg Prod.fst (hcell t)
  have hfine : ∀ t, small₂.1 (e t) = small₁.1 t := by
    intro t
    apply fine_pair_eq _ _ (congrArg Prod.snd (hcell t))
    calc
      MME.DWZTable2Counts.coarseOf (small₂.1 (e t)) =
          MME.DWZSquare.shapeZ (outer (e t)) := small₂.2.1 (e t)
      _ = MME.DWZSquare.shapeZ (outer t) := by rw [houter]
      _ = MME.DWZTable2Counts.coarseOf (small₁.1 t) :=
        (small₁.2.1 t).symm
  let g : UsefulBlockShuffleGroup outer := ⟨e, houter⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  funext t
  change small₁.1 (e.symm t) = small₂.1 t
  have h := hfine (e.symm t)
  simpa using h.symm
