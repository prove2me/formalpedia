-- Prove2me | solution 1 for mme_primary_hash_family_outerExtractionMap_modeOne_profile_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:57:03.307+00:00
-- url     : https://prove2.me/submissions/f86066f1-eeea-430a-a87f-e91c9c32e90c

import Theorems.Thm_mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data
import Definitions.Def_mme_dwz_q6_coupled_explicit_grading

open MME MME.TensorObj MME.DWZComponentRestriction
  PiTensorProduct BigOperators Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

private theorem functions_ne_at_of_fiber_card_ne
    {n : ℕ} {J : Type u} [Fintype J] [DecidableEq J]
    (f g : Fin n → J) (a : J)
    (hne : (Finset.univ.filter (fun r ↦ f r = a)).card ≠
      (Finset.univ.filter (fun r ↦ g r = a)).card) :
    ∃ r, f r ≠ g r := by
  by_contra hall
  push Not at hall
  have hfg : f = g := funext hall
  subst g
  exact hne rfl

theorem solution
    {K : Type u} [Field K]
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) (2 * N))
    (hnot : ¬ ∀ a : Fin 3,
      (Finset.univ.filter (fun r : Fin (2 * N) ↦
        dwzQ6CoupledCoordGrade 1
          (PowIndex.get (2 * N) w r).down = a)).card =
        cwQ6CoupledMarginalMultiplicity N L G 1 a) :
    outerExtractionMap (dwzQ6CoupledGrading K) family 1
        (kronPowModeBasis (coupledObj K 6) 1
          ((dwzQ6CoupledBasis K 1).reindex Equiv.ulift.symm)
          (2 * N) w) = 0 := by
  classical
  let G0 := dwzQ6CoupledGrading K
  let cB : Basis (ULift.{u} (Fin 6 ⊕ Fin 6)) K
      ((coupledObj K 6).V 1) :=
    (dwzQ6CoupledBasis K 1).reindex Equiv.ulift.symm
  let grade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 :=
    fun j ↦ dwzQ6CoupledCoordGrade 1 j.down
  have hGzero : ∀ (a : Fin 3) (j : ULift.{u} (Fin 6 ⊕ Fin 6)),
      grade j ≠ a → G0.blockProj 1 a (cB j) = 0 := by
    intro a j hne
    rw [show cB j = dwzQ6CoupledBasis K 1 j.down by
      exact Module.Basis.reindex_apply
        (dwzQ6CoupledBasis K 1) Equiv.ulift.symm j]
    apply TensorObj.TypeGrading.blockProj_apply_mem_ne G0 1 a
      (dwzQ6CoupledCoordGrade 1 j.down) (Ne.symm hne)
    exact Submodule.subset_span ⟨j.down, rfl, rfl⟩
  unfold outerExtractionMap
  simp only [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro p _
  have htarget (a : Fin 3) :
      (Finset.univ.filter (fun r : Fin (2 * N) ↦
        componentAddress family p.1 p.2 1 r = a)).card =
        cwQ6CoupledMarginalMultiplicity N L G 1 a := by
    rw [componentAddress_eq_entry]
    exact (family.entry (p.1, p.2)).2.2 1 a
  obtain ⟨a, ha⟩ := Classical.not_forall.mp hnot
  have hmismatch : ∃ r : Fin (2 * N),
      grade (PowIndex.get (2 * N) w r) ≠
        componentAddress family p.1 p.2 1 r := by
    apply functions_ne_at_of_fiber_card_ne
      (fun r ↦ grade (PowIndex.get (2 * N) w r))
      (fun r ↦ componentAddress family p.1 p.2 1 r) a
    intro heq
    exact ha (heq.trans (htarget a))
  have hp := mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
    G0 1 cB grade hGzero (2 * N)
    (componentAddress family p.1 p.2) w hmismatch
  change gradedBigAddSlot A (starObj G0 family) p.1 1
      (componentInclusion G0 family p.1 p.2 1
        (gradedAddressProj G0 (2 * N)
          (componentAddress family p.1 p.2) 1
          (kronPowModeBasis (coupledObj K 6) 1 cB (2 * N) w))) = 0
  rw [hp]
  calc
    _ = gradedBigAddSlot A (starObj G0 family) p.1 1 0 :=
      congrArg (gradedBigAddSlot A (starObj G0 family) p.1 1)
        ((componentInclusion G0 family p.1 p.2 1).map_zero)
    _ = 0 := (gradedBigAddSlot A (starObj G0 family) p.1 1).map_zero
