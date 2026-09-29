-- Prove2me | solution 1 for sourceBrokenFamily_restrict_of_xy_zero_and_singleton_cross_z_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T19:32:10.480043+00:00
-- url     : https://prove2.me/submissions/1ea409bc-29cc-44b8-aadb-3c8a91b4f916

import Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons
import Theorems.Thm_mme_dwz_source_broken_owner_projector_diagonal
import Theorems.Thm_mme_tensor_family_direct_sum_restrict_of_mixed_maps
import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_TypeGrading_kron

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

open MME.DWZSourceAligned

/-- Exact whole-family tensor assembly interface.  Mixed owners with unequal
X/Y choices are assumed annihilated by the global first-hash support test.
For the remaining equal-X/Y, distinct-Z case, it is enough to annihilate each
surviving singleton Z basis word separately. -/
theorem solution
    {K : Type u} [Field K] {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (hXYZero : ∀ js : Fin 3 → Fin k,
      js 0 ≠ js 1 →
      PiTensorProduct.map
          (fun i ↦
            ((brokenAddressGrading K m (outer (js i))
                (copy (js i))).blockProj i 0).comp
              (gradedAddressProj (cwSquareCanonicalGrading K 6) N
                (coarseAddress (outer (js i))) i))
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t = 0)
    (hSingletonCross : ∀ (js : Fin 3 → Fin k),
      js 0 = js 1 → js 0 ≠ js 2 →
      ∀ W : AddressZWord (outer (js 2)),
      addressWordSurvives m (outer (js 2)) (copy (js 2)) W →
      let S : TensorObj K 3 :=
        (TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N
      let maps : ∀ i : Fin 3, S.V i →ₗ[K]
          (brokenAddressObj K m (outer (js i)) (copy (js i))).V i :=
        fun i ↦
          ((brokenAddressGrading K m (outer (js i))
              (copy (js i))).blockProj i 0).comp
            (gradedAddressProj (cwSquareCanonicalGrading K 6) N
              (coarseAddress (outer (js i))) i)
      let singleton :=
        MME.DWZComponentRestriction.basisLabelProjection
          (coarseAddressZBasis K (outer (js 2))) id {W}
      PiTensorProduct.map
          (Function.update maps 2
            ((((brokenAddressGrading K m (outer (js 2))
                  (copy (js 2))).blockProj 2 0).comp singleton).comp
              (gradedAddressProj (cwSquareCanonicalGrading K 6) N
                (coarseAddress (outer (js 2))) 2))) S.t = 0) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦
        brokenAddressObj K m (outer j) (copy j)))
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N) := by
  classical
  let S : TensorObj K 3 :=
    (TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N
  let B : Fin k → TensorObj K 3 := fun j ↦
    brokenAddressObj K m (outer j) (copy j)
  let f : ∀ j : Fin k, ∀ i : Fin 3, S.V i →ₗ[K] (B j).V i :=
    fun j i ↦
      ((brokenAddressGrading K m (outer j) (copy j)).blockProj i 0).comp
        (gradedAddressProj (cwSquareCanonicalGrading K 6) N
          (coarseAddress (outer j)) i)
  apply mme_tensor_family_direct_sum_restrict_of_mixed_maps S B f
  · intro j
    dsimp only [S, B, f]
    exact mme_dwz_source_broken_owner_projector_diagonal
      m (outer j) (copy j)
  · intro js hnonconstant
    by_cases h01 : js 0 = js 1
    · have h02 : js 0 ≠ js 2 := by
        intro h02
        apply hnonconstant (js 0)
        funext i
        fin_cases i
        · rfl
        · exact h01.symm
        · exact h02.symm
      let U : TensorObj K 3 :=
        { V := fun i ↦ (B (js i)).V i
          t := 0 }
      let bZ := coarseAddressZBasis K (outer (js 2))
      let allowed := addressWordSurvives m (outer (js 2)) (copy (js 2))
      let : DecidablePred allowed := Classical.decPred _
      let preZ : S.V 2 →ₗ[K] (coarseAddressObj K (outer (js 2))).V 2 :=
        gradedAddressProj (cwSquareCanonicalGrading K 6) N
          (coarseAddress (outer (js 2))) 2
      let selectZ : (coarseAddressObj K (outer (js 2))).V 2 →ₗ[K] U.V 2 :=
        (brokenAddressGrading K m (outer (js 2))
          (copy (js 2))).blockProj 2 0
      let maps : ∀ i : Fin 3, S.V i →ₗ[K] U.V i :=
        fun i ↦ f (js i) i
      apply mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons
        bZ allowed preZ selectZ maps
      · rfl
      · intro W hW
        apply TensorObj.TypeGrading.blockProj_apply_mem_ne
          (brokenAddressGrading K m (outer (js 2)) (copy (js 2)))
          2 0 1 (by decide)
        change bZ W ∈ cwBasisGrade bZ
          (fun W' ↦ if allowed W' then 0 else 1) 1
        exact Submodule.subset_span
          ⟨W, by simp only [Set.mem_ofPred_eq, if_neg hW], rfl⟩
      · intro W hW
        exact hSingletonCross js h01 h02 W hW
    · dsimp only [S, f]
      exact hXYZero js h01
