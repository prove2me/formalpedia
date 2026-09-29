-- Prove2me | solution 1 for mme_dwz_table2_step1_fine_support_implies_grouped_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:02:59.49953+00:00
-- url     : https://prove2.me/submissions/73420993-4d48-47dd-820d-e9e3b0c9295a

import Theorems.Thm_mme_dwz_table2_step1_boundary_z_histogram_from_fine_support
import Theorems.Thm_mme_dwz_table2_step1_interior_z_histogram
import Theorems.Thm_mme_dwz_table2_boundary_interior_implies_grouped_compatibility

open MME MME.DWZStep1Support MME.DWZStep1Histogram

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (q m : ℕ)
    {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15)
    (left right : Fin 3 → Position → Fin 3)
    (hCoarse : ∀ i t,
      (left i t).val + (right i t).val =
        (![MME.DWZSquare.shapeX (outer t),
          MME.DWZSquare.shapeY (outer t),
          MME.DWZSquare.shapeZ (outer t)] i).val)
    (hFineSupport : ∀ t,
      (cwSquareFineSplitGrading K q).blockTensor
        (fun i => fineSplitGrade (left i t) (right i t)) ≠ 0)
    (hXSurvives : ∀ (s : Fin 15), MME.DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer t = s ∧ (left 0 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m)
    (hYSurvives : ∀ (s : Fin 15), MME.DWZSquare.shapeX s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer t = s ∧ (left 1 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m)
    (hTotal : ∀ (k : Fin 5) (a : Fin 3),
      Fintype.card (TotalZFiber outer (left 2) k a) =
        table2TotalZSplit k a * m) :
    let groupedRegion :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s =>
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
      Fintype.card
          {t : Position // groupedRegion (outer t) = r ∧ left 2 t = a} =
        MME.DWZTable2Cardinality.cellCount m r a := by
  have hBoundary :=
    mme_dwz_table2_step1_boundary_z_histogram_from_fine_support
      (K := K) q m outer left right hCoarse hFineSupport hXSurvives hYSurvives
  have hInterior := mme_dwz_table2_step1_interior_z_histogram
    m outer (left 2) hTotal hBoundary
  exact mme_dwz_table2_boundary_interior_implies_grouped_compatibility
    m outer (left 2) hBoundary hInterior
