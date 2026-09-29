-- Prove2me | solution 1 for mme_CW_square_fine_split_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:37:33.098128+00:00
-- url     : https://prove2.me/submissions/5a1f0bb2-eafa-4a4e-8504-c35e3706ce7a

import Theorems.Thm_mme_CW_three_canonical_support

open MME
open MME.DWZStep1Support

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (K : Type u) [Field K] (q : ℕ)
    (left right : Fin 3 → Fin 3)
    (h : (cwSquareFineSplitGrading K q).blockTensor
      (fun s => fineSplitGrade (left s) (right s)) ≠ 0) :
    ((left 0).val + (left 1).val + (left 2).val = 2) ∧
      ((right 0).val + (right 1).val + (right 2).val = 2) := by
  constructor
  · by_contra hsum
    have hleft := TensorObj.TypeGrading.kronGrading_blockTensor_ne_zero_left
      (cwThreeCanonicalGrading K q) (cwThreeCanonicalGrading K q)
      left right h
    exact hleft (mme_CW_three_canonical_support K q left hsum)
  · by_contra hsum
    have hright := TensorObj.TypeGrading.kronGrading_blockTensor_ne_zero_right
      (cwThreeCanonicalGrading K q) (cwThreeCanonicalGrading K q)
      left right h
    exact hright (mme_CW_three_canonical_support K q right hsum)
