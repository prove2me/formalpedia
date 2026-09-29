-- Prove2me | solution 1 for mme_dwz_table2_completed_useful_nonholes_direct_sum_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T12:27:54.806689+00:00
-- url     : https://prove2.me/submissions/c37378b8-35d6-4e87-9561-06c218469f07

import Theorems.Thm_mme_dwz_step2_nonholes_direct_sum_restrict
import Theorems.Thm_mme_dwz_table2_completed_useful_family_step1_premises
import Theorems.Thm_mme_dwz_table2_completed_useful_family_supported_compatible

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (K : Type u) [Field K] (q m N k : ℕ)
    (outer : Fin k → Fin N → Fin 15)
    [DecidableRel (retainedFineCompatible m outer)]
    (small : ∀ j : Fin k,
      MME.DWZTable2StandardForm.UsefulBlock m (outer j))
    (useful : (Fin N → Fin (3 * 3)) → Fin k → Prop)
    [DecidableRel useful]
    (hCommonZ : ∀ j j' r,
      DWZSquare.shapeZ (outer j r) = DWZSquare.shapeZ (outer j' r))
    (hYIsolated : ∀ j j',
      (fun r ↦ DWZSquare.shapeY (outer j r)) =
          (fun r ↦ DWZSquare.shapeY (outer j' r)) → j = j')
    (hNonhole :
      let left : Fin k → Fin 3 → Fin N → Fin 3 := fun j ↦
        completedFineLeft (outer j) (small j).1 (small j).2.1
      let right : Fin k → Fin 3 → Fin N → Fin 3 := fun j ↦
        completedFineRight (outer j) (small j).1 (small j).2.1
      ∀ j : Fin k,
        retainedFineAddress left right j 2 ∈
          (MME.DWZStep2.brokenCopy
            (retainedFineCompatible m outer) useful j).nonholes) :
    let left : Fin k → Fin 3 → Fin N → Fin 3 := fun j ↦
      completedFineLeft (outer j) (small j).1 (small j).2.1
    let right : Fin k → Fin 3 → Fin N → Fin 3 := fun j ↦
      completedFineRight (outer j) (small j).1 (small j).2.1
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ gradedAddressBlock
        (cwSquareFineSplitGrading K q)
        (retainedFineAddress left right j)))
      ((TensorObj.kron (CWObj K q) (CWObj K q)).kronPow N) := by
  classical
  dsimp only at hNonhole ⊢
  have hStep1 :=
    mme_dwz_table2_completed_useful_family_step1_premises m outer small
  apply mme_dwz_step2_nonholes_direct_sum_restrict
    (cwSquareFineSplitGrading K q)
    (retainedFineAddress
      (fun j ↦ completedFineLeft (outer j) (small j).1 (small j).2.1)
      (fun j ↦ completedFineRight (outer j) (small j).1 (small j).2.1))
    (retainedFineCompatible m outer) useful hNonhole
  · exact mme_dwz_table2_retained_fine_address_xy_owner K q outer
      (fun j ↦ completedFineLeft (outer j) (small j).1 (small j).2.1)
      (fun j ↦ completedFineRight (outer j) (small j).1 (small j).2.1)
      hStep1.1 hCommonZ hYIsolated
  · exact mme_dwz_table2_completed_useful_family_supported_compatible
      K q m outer small hCommonZ hYIsolated
