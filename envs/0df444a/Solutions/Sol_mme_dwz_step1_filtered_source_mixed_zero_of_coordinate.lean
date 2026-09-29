-- Prove2me | solution 1 for mme_dwz_step1_filtered_source_mixed_zero_of_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:05:28.871396+00:00
-- url     : https://prove2.me/submissions/c7d88f49-6480-4270-bff5-1168522838d8

import Theorems.Thm_mme_gradedAddressProj_then_post_map_eq_zero_of_coordinate
import Theorems.Thm_mme_gradedAddressBlockModeEquiv_comp_proj
import Definitions.Def_mme_dwz_step1_broken_owner_maps

open MME Module PiTensorProduct
open MME.DWZSourceAligned

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

private def b2MixedAddress {k N : ℕ}
    (outer : Fin k → Fin N → Fin 15) (js : Fin 3 → Fin k) :
    Fin 3 → Fin N → Fin 5 :=
  fun i r ↦ coarseAddress (outer (js i)) i r

private noncomputable def b2MixedModeEquiv
    (K : Type u) [Field K] {k N : ℕ}
    (outer : Fin k → Fin N → Fin 15) (js : Fin 3 → Fin k)
    (i : Fin 3) :
    (gradedAddressBlock (cwSquareCanonicalGrading K 6)
        (b2MixedAddress outer js)).V i ≃ₗ[K]
      (coarseAddressObj K (outer (js i))).V i := by
  exact CoupledCTensorPackaging.gradedAddressBlockModeEquiv
    (cwSquareCanonicalGrading K 6) N
    (b2MixedAddress outer js)
    (coarseAddress (outer (js i))) i (by rfl)

private noncomputable def b2MixedPost
    (K : Type u) [Field K] {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (js : Fin 3 → Fin k) :
    ∀ i : Fin 3,
      (gradedAddressBlock (cwSquareCanonicalGrading K 6)
          (b2MixedAddress outer js)).V i →ₗ[K]
        (brokenAddressObj K m (outer (js i)) (copy (js i))).V i :=
  fun i ↦
    (step1FilteredBrokenAddressMaps K m
      (outer (js i)) (copy (js i)) i).comp
        (b2MixedModeEquiv K outer js i).toLinearMap

private noncomputable def b2MixedSourceMaps
    (K : Type u) [Field K] (m : ℕ) {k N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (js : Fin 3 → Fin k) :
    ∀ i : Fin 3,
      (((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).V i) →ₗ[K]
        (brokenAddressObj K m (outer (js i)) (copy (js i))).V i :=
  fun i ↦
    (b2MixedPost K outer copy js i).comp
      (gradedAddressProj (cwSquareCanonicalGrading K 6) N
        (b2MixedAddress outer js) i)

private theorem b2MixedSourceMaps_eq_owner
    {K : Type u} [Field K] (m : ℕ) {k N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (js : Fin 3 → Fin k) (i : Fin 3) :
    b2MixedSourceMaps K m outer copy js i =
      step1FilteredBrokenSourceMaps K m
        (outer (js i)) (copy (js i)) i := by
  unfold b2MixedSourceMaps b2MixedPost step1FilteredBrokenSourceMaps
  rw [LinearMap.comp_assoc]
  unfold b2MixedModeEquiv
  have hproj := mme_gradedAddressBlockModeEquiv_comp_proj
    (cwSquareCanonicalGrading K 6)
    (b2MixedAddress outer js)
    (coarseAddress (outer (js i))) i rfl
  exact congrArg
    (fun g ↦ (step1FilteredBrokenAddressMaps K m
      (outer (js i)) (copy (js i)) i).comp g) hproj

private theorem b2Map_eq_of_pointwise
    {R : Type u} [CommSemiring R]
    {S T : Fin 3 → Type u}
    [∀ i, AddCommMonoid (S i)] [∀ i, Module R (S i)]
    [∀ i, AddCommMonoid (T i)] [∀ i, Module R (T i)]
    (f g : ∀ i, S i →ₗ[R] T i)
    (h : ∀ i, f i = g i)
    (x : PiTensorProduct R S) :
    PiTensorProduct.map f x = PiTensorProduct.map g x := by
  rw [funext h]

theorem solution
    {K : Type u} [Field K] {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (js : Fin 3 → Fin k) (r : Fin N)
    (hrzero :
      (cwSquareCanonicalGrading K 6).blockTensor
        (fun i ↦ coarseAddress (outer (js i)) i r) = 0) :
    PiTensorProduct.map
        (fun i ↦ step1FilteredBrokenSourceMaps K m
          (outer (js i)) (copy (js i)) i)
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t = 0 := by
  let T : TensorObj K 3 := TensorObj.kron (CWObj K 6) (CWObj K 6)
  have hr : (cwSquareCanonicalGrading K 6).blockTensor
      (fun i ↦ b2MixedAddress outer js i r) = 0 := by
    exact hrzero
  have hraw : PiTensorProduct.map
      (b2MixedSourceMaps K m outer copy js) (T.kronPow N).t = 0 := by
    exact mme_gradedAddressProj_then_post_map_eq_zero_of_coordinate
      (T := T) (t := 5) (n := N)
      (W := fun i ↦
        (brokenAddressObj K m (outer (js i)) (copy (js i))).V i)
      (cwSquareCanonicalGrading K 6) (b2MixedAddress outer js)
      (b2MixedPost K outer copy js) r hr
  have hmaps : PiTensorProduct.map
      (b2MixedSourceMaps K m outer copy js) (T.kronPow N).t =
      PiTensorProduct.map
        (fun i ↦ step1FilteredBrokenSourceMaps K m
          (outer (js i)) (copy (js i)) i)
        (T.kronPow N).t := by
    apply b2Map_eq_of_pointwise
    intro i
    exact b2MixedSourceMaps_eq_owner m outer copy js i
  exact hmaps.symm.trans hraw
