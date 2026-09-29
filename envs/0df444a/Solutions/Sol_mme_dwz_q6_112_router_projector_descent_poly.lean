-- Prove2me | solution 1 for mme_dwz_q6_112_router_projector_descent_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T21:35:28.92518+00:00
-- url     : https://prove2.me/submissions/c191ebba-3f3c-414b-8b15-7456f1184b4a

import Theorems.Thm_mme_dwz_q6_112_disallowed_word_mismatches_exact_address
import Theorems.Thm_mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
import Theorems.Thm_mme_kronPowModeMap_recursive_basis
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes

open MME MME.TensorObj MME.DWZComponentRestriction PiTensorProduct Module
open BigOperators

universe u w

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

theorem solution
    {K : Type u} [Field K] (m : ℕ)
    (C A : TensorObj K 3) (G : C.TypeGrading 3)
    {I : Type u} {J : Type w} [Fintype J]
    (cZ : Basis I K (C.V 2)) (targetGrade : I → Fin 3)
    (router : ∀ i : Fin 3,
      (canonicalComponentBlock K 12).V i →ₗ[K] C.V i)
    (label : LiftedCoarsePair.{u} 6 2 → I)
    (hrouterZ : ∀ p,
      router 2 (canonicalComponentZBasis K 12 p) = cZ (label p))
    (htranslate : ∀ p,
      p.leftGrade =
        mme_dwz_q6_coupled_Z_leftGrade (targetGrade (label p)))
    (exactAddress : J → CWQ6ExactCoupledAddress
      (50000000 * (20088623 * m))
      (21015 * (20088623 * m))
      (49978985 * (20088623 * m)))
    (address : J → Fin 3 →
      Fin (MME.DWZTable2Counts.component (12 : Fin 15) * m) → Fin 3)
    (haddress : ∀ (j : J)
      (hlen : MME.DWZTable2Counts.component (12 : Fin 15) * m =
        2 * (50000000 * (20088623 * m))) (i) (r),
      address j i r = (exactAddress j).1 i (Fin.cast hlen r))
    (post : ∀ j : J,
      (gradedAddressBlock G (address j)).V 2 →ₗ[K] A.V 2)
    (extract : ∀ i : Fin 3,
      (C.kronPow
        (MME.DWZTable2Counts.component (12 : Fin 15) * m)).V i →ₗ[K]
        A.V i)
    (hGzero : ∀ (a : Fin 3) (j : I), targetGrade j ≠ a →
      G.blockProj 2 a (cZ j) = 0)
    (hextractZ : extract 2 =
      ∑ j : J, (post j).comp
        (gradedAddressProj G
          (MME.DWZTable2Counts.component (12 : Fin 15) * m)
          (address j) 2))
    (hrouterPow :
      PiTensorProduct.map
          (fun i ↦ kronPowModeMap i (router i)
            (MME.DWZTable2Counts.component (12 : Fin 15) * m))
          ((canonicalComponentBlock K 12).kronPow
            (MME.DWZTable2Counts.component (12 : Fin 15) * m)).t =
        (C.kronPow
          (MME.DWZTable2Counts.component (12 : Fin 15) * m)).t)
    (hextractTensor :
      PiTensorProduct.map extract
          (C.kronPow
            (MME.DWZTable2Counts.component (12 : Fin 15) * m)).t =
        A.t) :
    TensorObj.Restrict A (restrictedComponentPower K 12 m) := by
  let n := MME.DWZTable2Counts.component (12 : Fin 15) * m
  let f : ∀ i : Fin 3,
      (((canonicalComponentBlock K 12).kronPow n).V i →ₗ[K] A.V i) :=
    fun i ↦ (extract i).comp (kronPowModeMap i (router i) n)
  have hfmap :
      PiTensorProduct.map f
          ((canonicalComponentBlock K 12).kronPow n).t = A.t := by
    calc
      _ = PiTensorProduct.map extract
          (PiTensorProduct.map
            (fun i ↦ kronPowModeMap i (router i) n)
            ((canonicalComponentBlock K 12).kronPow n).t) := by
              rw [PiTensorProduct.map_comp]
              rfl
      _ = PiTensorProduct.map extract (C.kronPow n).t := by
        rw [hrouterPow]
      _ = A.t := hextractTensor
  let : DecidablePred (componentWordAllowed (12 : Fin 15) m) :=
    Classical.decPred _
  have hrestrict := mme_restrict_basisZAllowedSubtensor_of_vanishes
    (((canonicalComponentBlock K 12).kronPow n)) A
    (componentPowerZBasis K 12 m) (componentWordAllowed 12 m)
    f hfmap
  apply hrestrict
  intro word hnot
  change extract 2
      (kronPowModeMap 2 (router 2) n
        (componentPowerZBasis K 12 m word)) = 0
  rw [hextractZ]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  apply Finset.sum_eq_zero
  intro j _
  change post j
      (gradedAddressProj G n (address j) 2
        (kronPowModeMap 2 (router 2) n
          (kronPowModeBasis (canonicalComponentBlock K 12) 2
            (canonicalComponentZBasis K 12) n word))) = 0
  rw [mme_kronPowModeMap_recursive_basis 2
    (canonicalComponentZBasis K 12) cZ (router 2) label hrouterZ]
  obtain ⟨hlen, r, hr⟩ :=
    mme_dwz_q6_112_disallowed_word_mismatches_exact_address
      m (exactAddress j) (fun p ↦ targetGrade (label p))
      htranslate word hnot
  have hmismatch : ∃ r : Fin n,
      targetGrade
          (PowIndex.get n
            (PowIndex.ofFun n
              (fun r ↦ label (PowIndex.get n word r))) r) ≠
        address j 2 r := by
    refine ⟨r, ?_⟩
    rw [PowIndex.get_ofFun]
    rw [haddress j hlen]
    exact hr
  have hp := mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
    G 2 cZ targetGrade hGzero n (address j)
    (PowIndex.ofFun n (fun r ↦ label (PowIndex.get n word r))) hmismatch
  calc
    _ = post j 0 := congrArg (post j) hp
    _ = 0 := (post j).map_zero
