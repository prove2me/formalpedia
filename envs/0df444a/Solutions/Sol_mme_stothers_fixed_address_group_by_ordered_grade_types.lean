-- Prove2me | solution 1 for mme_stothers_fixed_address_group_by_ordered_grade_types
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:08:51.326332+00:00
-- url     : https://prove2.me/submissions/113d4da8-9f2f-43f2-9436-915bed9cf5ae

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_fixed_outer_profile
import Theorems.Thm_mme_kronFin_group_by_exact_fibers_iso

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

/-! The first exact-address regrouping step is purely finite: reorder the
literal address coordinates by their ordered grade triple. -/

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) (a : MME.StothersFourth.FixedExactOuterAddress m) :
    let e : (Fin 3 → Fin 9) ≃ Fin 729 := by
      classical
      simpa only [Fintype.card_fun, Fintype.card_fin, Nat.reducePow] using
        (Fintype.equivFin (Fin 3 → Fin 9))
    TensorObj.Isomorphic
      (gradedAddressBlock
        (MME.StothersFourth.cwFourthCanonicalGrading K 6) a.1)
      (TensorObj.kronFin 729 (fun s ↦
        ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
          (e.symm s)).kronPow
            (MME.StothersFourth.fixedJointMultiplicity m (e.symm s)))) := by
  classical
  let e : (Fin 3 → Fin 9) ≃ Fin 729 := by
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.reducePow] using
      (Fintype.equivFin (Fin 3 → Fin 9))
  let X : Fin 729 → TensorObj K 3 := fun s ↦
    (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
      (e.symm s)
  let w : Fin (MME.StothersFourth.fixedOuterLength m) → Fin 729 :=
    fun j ↦ e (MME.StothersFourth.fixedAddressType a.1 j)
  let multiplicity : Fin 729 → ℕ := fun s ↦
    MME.StothersFourth.fixedJointMultiplicity m (e.symm s)
  have hcard : ∀ s : Fin 729,
      Fintype.card {j : Fin (MME.StothersFourth.fixedOuterLength m) //
        w j = s} = multiplicity s := by
    intro s
    rw [Fintype.card_subtype]
    simpa only [w, multiplicity, e, Equiv.eq_symm_apply] using
      a.2 (e.symm s)
  have hgroup := mme_kronFin_group_by_exact_fibers_iso X w multiplicity hcard
  have hAT : ∀ k : Fin (MME.StothersFourth.fixedOuterLength m),
      MME.StothersFourth.fixedAddressType a.1 k = fun i ↦ a.1 i k := fun _ ↦ rfl
  simpa only [gradedAddressBlock, X, w, multiplicity,
    hAT, Equiv.symm_apply_apply] using hgroup
