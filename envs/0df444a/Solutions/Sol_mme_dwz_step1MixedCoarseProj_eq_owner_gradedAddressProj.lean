-- Prove2me | solution 1 for mme_dwz_step1MixedCoarseProj_eq_owner_gradedAddressProj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T10:35:45.953371+00:00
-- url     : https://prove2.me/submissions/cea2d9a4-624e-44fc-9c50-261758e7a52f

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

private theorem addressModeEquiv_comp_proj_local
    {K : Type u} [Field K]
    {t R : ℕ} {X : TensorObj K 3} (G0 : X.TypeGrading t)
    (address address' : Fin 3 → Fin R → Fin t)
    (i : Fin 3) (hi : address i = address' i) :
    (CoupledCTensorPackaging.gradedAddressBlockModeEquiv
      G0 R address address' i hi).toLinearMap.comp
        (gradedAddressProj G0 R address i) =
      gradedAddressProj G0 R address' i := by
  induction R with
  | zero => rfl
  | succ R ih =>
      simp only [CoupledCTensorPackaging.gradedAddressBlockModeEquiv,
        gradedAddressProj]
      apply TensorProduct.ext'
      intro x y
      change
        (LinearEquiv.ofEq
          (G0.classOf i (address i 0))
          (G0.classOf i (address' i 0)) _
          (G0.blockProj i (address i 0) x)) ⊗ₜ[K]
            (CoupledCTensorPackaging.gradedAddressBlockModeEquiv G0 R
              (fun i' j => address i' j.succ)
              (fun i' j => address' i' j.succ) i _)
              (gradedAddressProj G0 R
                (fun i' j => address i' j.succ) i y) =
          (G0.blockProj i (address' i 0) x) ⊗ₜ[K]
            gradedAddressProj G0 R
              (fun i' j => address' i' j.succ) i y
      congr 1
      · have h0 : address i 0 = address' i 0 := congrFun hi 0
        apply Subtype.ext
        change
          ((G0.blockProj i (address i 0) x :
              G0.classOf i (address i 0)) : X.V i) =
            ((G0.blockProj i (address' i 0) x :
              G0.classOf i (address' i 0)) : X.V i)
        exact congrArg
          (fun r : Fin t =>
            ((G0.blockProj i r x : G0.classOf i r) : X.V i)) h0
      · have htail :
            (fun j : Fin R => address i j.succ) =
              (fun j : Fin R => address' i j.succ) := by
          funext j
          exact congrFun hi j.succ
        have hih := ih
          (fun i' j => address i' j.succ)
          (fun i' j => address' i' j.succ) htail
        exact LinearMap.congr_fun hih y

/-!
# Mixed coarse projection normal form

The mixed-address block differs from the ordinary coarse-address block of a
mode's owner only by a canonical equality transport.  Composing that
transport with the mixed projection therefore gives the ordinary owner
projection literally.  This is the map identity needed to turn the paired
mixed-singleton theorem into the `Function.update` family used by the final
direct-sum assembly.
-/

theorem solution
    {K : Type u} [Field K] {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n) (i : Fin 3) :
    step1MixedCoarseProj K reindex edge competitor owner i =
      gradedAddressProj (cwSquareCanonicalGrading K 6) L
        (coarseAddress
          (sourceWord reindex edge
            (step1MixedOwnerIndex competitor owner i))) i := by
  unfold step1MixedCoarseProj step1MixedModeEquiv
  exact addressModeEquiv_comp_proj_local
    (cwSquareCanonicalGrading K 6)
    (step1MixedAddress reindex edge competitor owner)
    (coarseAddress
      (sourceWord reindex edge
      (step1MixedOwnerIndex competitor owner i))) i rfl
