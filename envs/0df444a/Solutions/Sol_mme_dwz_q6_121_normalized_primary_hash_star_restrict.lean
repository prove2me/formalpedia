-- Prove2me | solution 1 for mme_dwz_q6_121_normalized_primary_hash_star_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T13:19:30.022124+00:00
-- url     : https://prove2.me/submissions/b61374f2-c3f1-4198-b56a-8f3c72b6d36c

import Theorems.Thm_mme_dwz_q6_canonical_121_211_powered_basis_labelled_source_routers
import Theorems.Thm_mme_primary_hash_family_permuted_outer_extraction_exact
import Theorems.Thm_mme_perm_kronPow_mode_equiv_recursive_basis
import Theorems.Thm_mme_dwz_q6_121_outerExtractionMap_mode0_vanishes_on_disallowed_word
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_dwz_q6_explicit_coupled_four_block_support
import Definitions.Def_mme_permutation
import Mathlib.Tactic

open MME MME.TensorObj MME.DWZComponentRestriction
  PiTensorProduct BigOperators Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

private theorem permObj_trans_iso_pair_row121
    {K : Type u} [Field K] {d : ℕ}
    (e e' : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.permObj e' (TensorObj.permObj e X))
      (TensorObj.permObj (e.trans e') X) := by
  have ht : (TensorObj.permObj e' (TensorObj.permObj e X)).t =
      (TensorObj.permObj (e.trans e') X).t := by
    exact PiTensorProduct.reindex_reindex e e' X.t
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (TensorObj.permObj (e.trans e') X).V))
      (TensorObj.permObj (e.trans e') X).t
    exact hmap.trans ht.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (TensorObj.permObj e' (TensorObj.permObj e X)).V))
      (TensorObj.permObj e' (TensorObj.permObj e X)).t
    exact hmap.trans ht

private theorem permObj_refl_iso_row121
    {K : Type u} [Field K] {d : ℕ} (X : TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.permObj (Equiv.refl (Fin d)) X) X := by
  have ht : (TensorObj.permObj (Equiv.refl (Fin d)) X).t = X.t := by
    change (PiTensorProduct.reindex K X.V (Equiv.refl (Fin d))) X.t = X.t
    rw [PiTensorProduct.reindex_refl]
    rfl
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id (R := K) (s := X.V)) X.t
    exact hmap.trans ht.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (TensorObj.permObj (Equiv.refl (Fin d)) X).V))
      (TensorObj.permObj (Equiv.refl (Fin d)) X).t
    exact hmap.trans ht

/-- The shared-Z star family selected by an exact primary family is a
restriction of the cyclically normalized literal row-121 component. -/
theorem mme_dwz_q6_121_normalized_primary_hash_star_restrict
    {K : Type u} [Field K]
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (1036722900000000 * m) L G A H) :
    TensorObj.Restrict
      (TensorObj.bigAdd
        (starObj (dwzQ6CoupledGrading K) family))
      (TensorObj.permObj cyclicPerm
        (restrictedComponentPower K (13 : Fin 15) m)) := by
  classical
  let N : ℕ := 1036722900000000 * m
  let n : ℕ := 2 * N
  let e : Equiv.Perm (Fin 3) := cyclicPerm.trans cyclicPerm
  let G0 := dwzQ6CoupledGrading K
  let stars : Fin A → TensorObj K 3 := starObj G0 family
  obtain ⟨coord, hcoord, ⟨router, hrouterTensor, hrouterZ⟩, _⟩ :=
    mme_dwz_q6_canonical_121_211_powered_basis_labelled_source_routers K n
  let extract : ∀ i : Fin 3,
      ((TensorObj.permObj e (coupledObj K 6)).kronPow n).V i →ₗ[K]
        (TensorObj.permObj e (TensorObj.bigAdd stars)).V i := fun i ↦
    (outerExtractionMap G0 family (e.symm i)).comp
      (permKronPowModeEquiv e (coupledObj K 6) i n).toLinearMap
  have hextractTensor : PiTensorProduct.map extract
        ((TensorObj.permObj e (coupledObj K 6)).kronPow n).t =
      (TensorObj.permObj e (TensorObj.bigAdd stars)).t := by
    simpa [N, n, e, G0, stars, extract] using
      mme_primary_hash_family_permuted_outer_extraction_exact
        G0 family
        (mme_dwz_q6_explicit_coupled_four_block_support (K := K)) e
  let f : ∀ i : Fin 3,
      ((canonicalComponentBlock K (13 : Fin 15)).kronPow n).V i →ₗ[K]
        (TensorObj.permObj e (TensorObj.bigAdd stars)).V i := fun i ↦
    (extract i).comp (router i)
  have hfmap : PiTensorProduct.map f
        ((canonicalComponentBlock K (13 : Fin 15)).kronPow n).t =
      (TensorObj.permObj e (TensorObj.bigAdd stars)).t := by
    calc
      _ = PiTensorProduct.map extract
          (PiTensorProduct.map router
            ((canonicalComponentBlock K (13 : Fin 15)).kronPow n).t) := by
        rw [PiTensorProduct.map_comp]
        rfl
      _ = PiTensorProduct.map extract
          ((TensorObj.permObj e (coupledObj K 6)).kronPow n).t := by
        rw [hrouterTensor]
      _ = _ := hextractTensor
  let b : Basis
      (PowIndex (LiftedCoarsePair.{u} 6 1) n) K
      (((canonicalComponentBlock K (13 : Fin 15)).kronPow n).V 2) :=
    kronPowModeBasis (canonicalComponentBlock K 13) 2
      (canonicalComponentZBasis K 13) n
  let allowed : PowIndex (LiftedCoarsePair.{u} 6 1) n → Prop := fun w ↦
    ∀ a : Fin 3,
      Fintype.card {r : Fin n // (PowIndex.get n w r).leftGrade = a} =
        MME.DWZTable2Counts.split (13 : Fin 15) a * m
  let : DecidablePred allowed := Classical.decPred _
  have hvanish : ∀ w, ¬ allowed w → f 2 (b w) = 0 := by
    intro w hnot
    change extract 2
      (router 2
        (kronPowModeBasis (canonicalComponentBlock K 13) 2
          (canonicalComponentZBasis K 13) n w)) = 0
    rw [hrouterZ w]
    change outerExtractionMap G0 family (e.symm 2)
      (permKronPowModeEquiv e (coupledObj K 6) 2 n
        (kronPowModeBasis (TensorObj.permObj e (coupledObj K 6)) 2
          ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) n
          (PowIndex.ofFun n
            (fun r ↦ ULift.up (coord (PowIndex.get n w r)))))) = 0
    refine (congrArg (fun x ↦ outerExtractionMap G0 family (e.symm 2) x)
      (mme_perm_kronPow_mode_equiv_recursive_basis e (coupledObj K 6) 2
        ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) n
        (PowIndex.ofFun n
          (fun r ↦ ULift.up (coord (PowIndex.get n w r)))))).trans ?_
    change outerExtractionMap G0 family 0
      (kronPowModeBasis (coupledObj K 6) 0
        ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) n
        (PowIndex.ofFun n
          (fun r ↦ ULift.up (coord (PowIndex.get n w r))))) = 0
    exact mme_dwz_q6_121_outerExtractionMap_mode0_vanishes_on_disallowed_word
      m L G A H family coord hcoord w hnot
  have hraw := mme_restrict_basisZAllowedSubtensor_of_vanishes
    ((canonicalComponentBlock K (13 : Fin 15)).kronPow n)
    (TensorObj.permObj e (TensorObj.bigAdd stars)) b allowed
    f hfmap hvanish
  have hn : MME.DWZTable2Counts.component (13 : Fin 15) * m = n := by
    change 2073445800000000 * m = 2 * (1036722900000000 * m)
    ring
  have hsourceEq :
      TensorObj.basisZAllowedSubtensor
          ((canonicalComponentBlock K (13 : Fin 15)).kronPow n) b allowed =
        restrictedComponentPower K (13 : Fin 15) m := by
    unfold restrictedComponentPower componentPowerProjectionGrading
      componentPowerZBasis componentWordAllowed
      TensorObj.basisZAllowedSubtensor
    rw [hn]
    rfl
  have hraw' : TensorObj.Restrict
      (TensorObj.permObj e (TensorObj.bigAdd stars))
      (restrictedComponentPower K (13 : Fin 15) m) := by
    rw [← hsourceEq]
    exact hraw
  have hpermuted := TensorObj.permObj_restrict cyclicPerm hraw'
  have hcycle : e.trans cyclicPerm = Equiv.refl (Fin 3) := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  have horient : TensorObj.Isomorphic
      (TensorObj.permObj cyclicPerm
        (TensorObj.permObj e (TensorObj.bigAdd stars)))
      (TensorObj.bigAdd stars) := by
    have htrans := permObj_trans_iso_pair_row121 e cyclicPerm
      (TensorObj.bigAdd stars)
    rw [hcycle] at htrans
    exact htrans.trans (permObj_refl_iso_row121 (TensorObj.bigAdd stars))
  exact TensorObj.Restrict.trans horient.2 hpermuted

theorem solution
    {K : Type u} [Field K]
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (1036722900000000 * m) L G A H) :
    TensorObj.Restrict
      (TensorObj.bigAdd
        (starObj (dwzQ6CoupledGrading K) family))
      (TensorObj.permObj cyclicPerm
        (restrictedComponentPower K (13 : Fin 15) m)) :=
  mme_dwz_q6_121_normalized_primary_hash_star_restrict
    m L G A H family
