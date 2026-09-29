-- Prove2me | solution 1 for mme_dwz_q6_canonical_121_211_powered_basis_labelled_source_routers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T10:07:33.44222+00:00
-- url     : https://prove2.me/submissions/9b220032-01dc-465f-80f4-2ba9c49d00b6

import Theorems.Thm_mme_dwz_q6_canonical_121_211_basis_labelled_source_routers
import Theorems.Thm_mme_kronPow_modewise_maps_preserve_tensor
import Theorems.Thm_mme_kronPowModeMap_recursive_basis

open MME MME.TensorObj MME.DWZComponentRestriction PiTensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

/-- The exact row-13/14 canonical routers lifted to a common arbitrary
Kronecker-power length, including their recursive Z-word basis action. -/
theorem mme_dwz_q6_canonical_121_211_powered_basis_labelled_source_routers
    (K : Type u) [Field K] (n : ℕ) :
    ∃ coord : LiftedCoarsePair.{u} 6 1 ≃ (Fin 6 ⊕ Fin 6),
      (∀ p,
        p.leftGrade =
          Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
            (fun _ : Fin 6 ↦ (1 : Fin 3)) (coord p)) ∧
      (∃ maps : ∀ i : Fin 3,
          ((canonicalComponentBlock K (13 : Fin 15)).kronPow n).V i →ₗ[K]
            ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
              (coupledObj K 6)).kronPow n).V i,
        PiTensorProduct.map maps
            ((canonicalComponentBlock K (13 : Fin 15)).kronPow n).t =
          ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)).kronPow n).t ∧
        ∀ w : PowIndex (LiftedCoarsePair.{u} 6 1) n,
          maps 2
              (kronPowModeBasis
                (canonicalComponentBlock K (13 : Fin 15)) 2
                (canonicalComponentZBasis K (13 : Fin 15)) n w) =
            kronPowModeBasis
              (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
                (coupledObj K 6)) 2
              ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex
                Equiv.ulift.symm) n
              (PowIndex.ofFun n
                (fun r ↦ ULift.up (coord (PowIndex.get n w r))))) ∧
      (∃ maps : ∀ i : Fin 3,
          ((canonicalComponentBlock K (14 : Fin 15)).kronPow n).V i →ₗ[K]
            ((TensorObj.permObj cyclicPerm
              (coupledObj K 6)).kronPow n).V i,
        PiTensorProduct.map maps
            ((canonicalComponentBlock K (14 : Fin 15)).kronPow n).t =
          ((TensorObj.permObj cyclicPerm
            (coupledObj K 6)).kronPow n).t ∧
        ∀ w : PowIndex (LiftedCoarsePair.{u} 6 1) n,
          maps 2
              (kronPowModeBasis
                (canonicalComponentBlock K (14 : Fin 15)) 2
                (canonicalComponentZBasis K (14 : Fin 15)) n w) =
            kronPowModeBasis
              (TensorObj.permObj cyclicPerm (coupledObj K 6)) 2
              ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex
                Equiv.ulift.symm) n
              (PowIndex.ofFun n
                (fun r ↦ ULift.up (coord (PowIndex.get n w r))))) := by
  obtain ⟨coord, hcoord, ⟨f13, hf13, hf13Z⟩, ⟨f14, hf14, hf14Z⟩⟩ :=
    mme_dwz_q6_canonical_121_211_basis_labelled_source_routers K
  let r13 : ∀ i : Fin 3,
      (canonicalComponentBlock K (13 : Fin 15)).V i →ₗ[K]
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6)).V i := fun i ↦ f13 i
  let r14 : ∀ i : Fin 3,
      (canonicalComponentBlock K (14 : Fin 15)).V i →ₗ[K]
        (TensorObj.permObj cyclicPerm (coupledObj K 6)).V i := fun i ↦ f14 i
  have hr13 : PiTensorProduct.map r13
        (canonicalComponentBlock K (13 : Fin 15)).t =
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
        (coupledObj K 6)).t := by
    exact hf13
  have hr14 : PiTensorProduct.map r14
        (canonicalComponentBlock K (14 : Fin 15)).t =
      (TensorObj.permObj cyclicPerm (coupledObj K 6)).t := by
    exact hf14
  let maps13 : ∀ i : Fin 3,
      ((canonicalComponentBlock K (13 : Fin 15)).kronPow n).V i →ₗ[K]
        ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6)).kronPow n).V i := fun i ↦
    kronPowModeMap i (r13 i) n
  let maps14 : ∀ i : Fin 3,
      ((canonicalComponentBlock K (14 : Fin 15)).kronPow n).V i →ₗ[K]
        ((TensorObj.permObj cyclicPerm
          (coupledObj K 6)).kronPow n).V i := fun i ↦
    kronPowModeMap i (r14 i) n
  refine ⟨coord, hcoord, ⟨maps13, ?_, ?_⟩, ⟨maps14, ?_, ?_⟩⟩
  · exact mme_kronPow_modewise_maps_preserve_tensor r13 hr13 n
  · intro w
    dsimp only [maps13]
    have hb : ∀ p : LiftedCoarsePair.{u} 6 1,
        r13 2 (canonicalComponentZBasis K (13 : Fin 15) p) =
          ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex
            Equiv.ulift.symm) (ULift.up (coord p)) := by
      intro p
      rw [Module.Basis.reindex_apply]
      simp only [r13, Pi.basisFun_apply]
      exact hf13Z p
    exact mme_kronPowModeMap_recursive_basis
      (T := canonicalComponentBlock K (13 : Fin 15))
      (S := TensorObj.permObj (cyclicPerm.trans cyclicPerm)
        (coupledObj K 6)) 2
      (canonicalComponentZBasis K (13 : Fin 15))
      ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm)
      (r13 2) (fun p ↦ ULift.up (coord p)) hb n w
  · exact mme_kronPow_modewise_maps_preserve_tensor r14 hr14 n
  · intro w
    dsimp only [maps14]
    have hb : ∀ p : LiftedCoarsePair.{u} 6 1,
        r14 2 (canonicalComponentZBasis K (14 : Fin 15) p) =
          ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex
            Equiv.ulift.symm) (ULift.up (coord p)) := by
      intro p
      rw [Module.Basis.reindex_apply]
      simp only [r14, Pi.basisFun_apply]
      exact hf14Z p
    exact mme_kronPowModeMap_recursive_basis
      (T := canonicalComponentBlock K (14 : Fin 15))
      (S := TensorObj.permObj cyclicPerm (coupledObj K 6)) 2
      (canonicalComponentZBasis K (14 : Fin 15))
      ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm)
      (r14 2) (fun p ↦ ULift.up (coord p)) hb n w

theorem solution (K : Type u) [Field K] (n : ℕ) :
    ∃ coord : LiftedCoarsePair.{u} 6 1 ≃ (Fin 6 ⊕ Fin 6),
      (∀ p,
        p.leftGrade =
          Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
            (fun _ : Fin 6 ↦ (1 : Fin 3)) (coord p)) ∧
      (∃ maps : ∀ i : Fin 3,
          ((canonicalComponentBlock K (13 : Fin 15)).kronPow n).V i →ₗ[K]
            ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
              (coupledObj K 6)).kronPow n).V i,
        PiTensorProduct.map maps
            ((canonicalComponentBlock K (13 : Fin 15)).kronPow n).t =
          ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)).kronPow n).t ∧
        ∀ w : PowIndex (LiftedCoarsePair.{u} 6 1) n,
          maps 2
              (kronPowModeBasis
                (canonicalComponentBlock K (13 : Fin 15)) 2
                (canonicalComponentZBasis K (13 : Fin 15)) n w) =
            kronPowModeBasis
              (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
                (coupledObj K 6)) 2
              ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex
                Equiv.ulift.symm) n
              (PowIndex.ofFun n
                (fun r ↦ ULift.up (coord (PowIndex.get n w r))))) ∧
      (∃ maps : ∀ i : Fin 3,
          ((canonicalComponentBlock K (14 : Fin 15)).kronPow n).V i →ₗ[K]
            ((TensorObj.permObj cyclicPerm
              (coupledObj K 6)).kronPow n).V i,
        PiTensorProduct.map maps
            ((canonicalComponentBlock K (14 : Fin 15)).kronPow n).t =
          ((TensorObj.permObj cyclicPerm
            (coupledObj K 6)).kronPow n).t ∧
        ∀ w : PowIndex (LiftedCoarsePair.{u} 6 1) n,
          maps 2
              (kronPowModeBasis
                (canonicalComponentBlock K (14 : Fin 15)) 2
                (canonicalComponentZBasis K (14 : Fin 15)) n w) =
            kronPowModeBasis
              (TensorObj.permObj cyclicPerm (coupledObj K 6)) 2
              ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex
                Equiv.ulift.symm) n
              (PowIndex.ofFun n
                (fun r ↦ ULift.up (coord (PowIndex.get n w r))))) :=
  mme_dwz_q6_canonical_121_211_powered_basis_labelled_source_routers K n
