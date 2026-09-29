-- Prove2me | solution 1 for mme_dwz_table2_retained_fine_address_xy_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T09:18:41.73454+00:00
-- url     : https://prove2.me/submissions/ab5d24eb-e05d-4003-b469-91387cb288e3

import Definitions.Def_mme_dwz_retained_fine_address
import Theorems.Thm_mme_CW_square_fine_split_support
import Definitions.Def_mme_dwz_square_data

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (K : Type u) [Field K] (q : ℕ)
    {Copy Position : Type*}
    (outer : Copy → Position → Fin 15)
    (left right : Copy → Fin 3 → Position → Fin 3)
    (hCoarse : ∀ j i r,
      (left j i r).val + (right j i r).val =
        (cwSquareBlockType
          (DWZSquare.shapeX (outer j r))
          (DWZSquare.shapeY (outer j r))
          (DWZSquare.shapeZ (outer j r)) i).val)
    (hCommonZ : ∀ j j' r,
      DWZSquare.shapeZ (outer j r) = DWZSquare.shapeZ (outer j' r))
    (hYIsolated : ∀ j j',
      (fun r ↦ DWZSquare.shapeY (outer j r)) =
        (fun r ↦ DWZSquare.shapeY (outer j' r)) → j = j') :
    ∀ js : Fin 3 → Copy,
      (∀ r : Position,
        (cwSquareFineSplitGrading K q).blockTensor
          (fun i ↦ retainedFineAddress left right (js i) i r) ≠ 0) →
      js 0 = js 1 := by
  intro js hSupported
  apply hYIsolated
  funext r
  apply Fin.ext
  have hFine := mme_CW_square_fine_split_support K q
    (fun i ↦ left (js i) i r)
    (fun i ↦ right (js i) i r) (by
      exact hSupported r)
  have hX := hCoarse (js 0) 0 r
  have hY := hCoarse (js 1) 1 r
  have hZ := hCoarse (js 2) 2 r
  simp only [cwSquareBlockType] at hX hY hZ
  have hCommonZval := congrArg Fin.val (hCommonZ (js 2) (js 0) r)
  have hShape := DWZSquare.shape_sum (outer (js 0) r)
  have hLeft :
      (left (js 0) 0 r).val + (left (js 1) 1 r).val +
          (left (js 2) 2 r).val = 2 := by
    simpa using hFine.1
  have hRight :
      (right (js 0) 0 r).val + (right (js 1) 1 r).val +
          (right (js 2) 2 r).val = 2 := by
    simpa using hFine.2
  have hMixed :
      (DWZSquare.shapeX (outer (js 0) r)).val +
          (DWZSquare.shapeY (outer (js 1) r)).val +
          (DWZSquare.shapeZ (outer (js 2) r)).val = 4 := by
    omega
  omega
