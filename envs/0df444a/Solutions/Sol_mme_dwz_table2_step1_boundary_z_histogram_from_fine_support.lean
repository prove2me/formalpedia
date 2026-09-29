-- Prove2me | solution 1 for mme_dwz_table2_step1_boundary_z_histogram_from_fine_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:41:02.288409+00:00
-- url     : https://prove2.me/submissions/86efe27f-1baf-4008-b3f1-c3af5d1a94b8

import Theorems.Thm_mme_CW_square_fine_split_support
import Definitions.Def_mme_dwz_table2_split_assignments

namespace MME.DWZStep1Support

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

/-- The three coarse grades of one Table-2 component. -/
private def table2Shape (s : Fin 15) : Fin 3 → Fin 5 :=
  ![MME.DWZSquare.shapeX s, MME.DWZSquare.shapeY s,
    MME.DWZSquare.shapeZ s]

/-- The left and right level-one grades of a fine nine-grade add to the
corresponding coarse Table-2 grade. -/
private def FineAddressCoarsens
    {Position : Type*}
    (outer : Position → Fin 15)
    (fine : Fin 3 → Position → Fin (3 * 3)) : Prop :=
  ∀ i t,
    (fineSplitLeft (fine i t)).val +
      (fineSplitRight (fine i t)).val =
        (table2Shape (outer t) i).val

/-- Pointwise nonzero fine blocks supply the support equations in both
level-one halves. -/
private theorem fine_block_support_equations
    {K : Type u} [Field K] (q : ℕ)
    {Position : Type*}
    (left right : Fin 3 → Position → Fin 3)
    (hSupport : ∀ t,
      (cwSquareFineSplitGrading K q).blockTensor
        (fun i => fineSplitGrade (left i t) (right i t)) ≠ 0) :
    (∀ t,
      (left 0 t).val + (left 1 t).val + (left 2 t).val = 2) ∧
    (∀ t,
      (right 0 t).val + (right 1 t).val + (right 2 t).val = 2) := by
  constructor <;> intro t
  · have hs := mme_CW_square_fine_split_support K q
      (fun i => left i t) (fun i => right i t) (hSupport t)
    exact hs.1
  · have hs := mme_CW_square_fine_split_support K q
      (fun i => left i t) (fun i => right i t) (hSupport t)
    exact hs.2

private abbrev boundaryXFiber
    {Position : Type*}
    (outer : Position → Fin 15)
    (left : Fin 3 → Position → Fin 3)
    (s : Fin 15) (a : Fin 3) :=
  {t : Position // outer t = s ∧ (left 0 t).val + a.val = 2}

private abbrev boundaryYFiber
    {Position : Type*}
    (outer : Position → Fin 15)
    (left : Fin 3 → Position → Fin 3)
    (s : Fin 15) (a : Fin 3) :=
  {t : Position // outer t = s ∧ (left 1 t).val + a.val = 2}

private abbrev boundaryZFiber
    {Position : Type*}
    (outer : Position → Fin 15)
    (left : Fin 3 → Position → Fin 3)
    (s : Fin 15) (a : Fin 3) :=
  {t : Position // outer t = s ∧ left 2 t = a}

private def xToZFiberEquiv
    {Position : Type*}
    (outer : Position → Fin 15)
    (left right : Fin 3 → Position → Fin 3)
    (hCoarse : ∀ i t,
      (left i t).val + (right i t).val =
        (table2Shape (outer t) i).val)
    (hLeftSupport : ∀ t,
      (left 0 t).val + (left 1 t).val + (left 2 t).val = 2)
    (s : Fin 15) (hsY : MME.DWZSquare.shapeY s = 0)
    (a : Fin 3) :
    boundaryXFiber outer left s a ≃ boundaryZFiber outer left s a where
  toFun t := ⟨t.1, t.2.1, by
    apply Fin.ext
    have hy := hCoarse 1 t.1
    rw [t.2.1] at hy
    have hs := hLeftSupport t.1
    have hxa : (left 0 t.1).val + a.val = 2 := t.2.2
    simp [table2Shape, hsY] at hy
    omega⟩
  invFun t := ⟨t.1, t.2.1, by
    have hy := hCoarse 1 t.1
    rw [t.2.1] at hy
    have hs := hLeftSupport t.1
    have hz := congrArg Fin.val t.2.2
    simp [table2Shape, hsY] at hy
    omega⟩
  left_inv t := by rfl
  right_inv t := by rfl

private def yToZFiberEquiv
    {Position : Type*}
    (outer : Position → Fin 15)
    (left right : Fin 3 → Position → Fin 3)
    (hCoarse : ∀ i t,
      (left i t).val + (right i t).val =
        (table2Shape (outer t) i).val)
    (hLeftSupport : ∀ t,
      (left 0 t).val + (left 1 t).val + (left 2 t).val = 2)
    (s : Fin 15) (hsX : MME.DWZSquare.shapeX s = 0)
    (a : Fin 3) :
    boundaryYFiber outer left s a ≃ boundaryZFiber outer left s a where
  toFun t := ⟨t.1, t.2.1, by
    apply Fin.ext
    have hx := hCoarse 0 t.1
    rw [t.2.1] at hx
    have hs := hLeftSupport t.1
    have hya : (left 1 t.1).val + a.val = 2 := t.2.2
    simp [table2Shape, hsX] at hx
    omega⟩
  invFun t := ⟨t.1, t.2.1, by
    have hx := hCoarse 0 t.1
    rw [t.2.1] at hx
    have hs := hLeftSupport t.1
    have hz := congrArg Fin.val t.2.2
    simp [table2Shape, hsX] at hx
    omega⟩
  left_inv t := by rfl
  right_inv t := by rfl

/-- **DWZ Additional Zeroing-Out Step 1, boundary reflection.**

At a boundary component, one coarse mode has grade zero.  The fine CW support
equation therefore forces the small Z split to be the reflected surviving X
or Y split.  Hence the Step-1 X/Y histogram rule gives the exact Table-2 Z
histogram component by component. -/
private theorem table2_step1_boundary_z_histogram
    (m : ℕ)
    {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15)
    (left right : Fin 3 → Position → Fin 3)
    (hCoarse : ∀ i t,
      (left i t).val + (right i t).val =
        (table2Shape (outer t) i).val)
    (hLeftSupport : ∀ t,
      (left 0 t).val + (left 1 t).val + (left 2 t).val = 2)
    (hXSurvives : ∀ (s : Fin 15), MME.DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card (boundaryXFiber outer left s a) =
          MME.DWZTable2Counts.split s a * m)
    (hYSurvives : ∀ (s : Fin 15), MME.DWZSquare.shapeX s = 0 →
      ∀ a : Fin 3,
        Fintype.card (boundaryYFiber outer left s a) =
          MME.DWZTable2Counts.split s a * m) :
    ∀ (s : Fin 15),
      MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card (boundaryZFiber outer left s a) =
          MME.DWZTable2Counts.split s a * m := by
  intro s hs a
  rcases hs with hsX | hsY
  · rw [← Fintype.card_congr
      (yToZFiberEquiv outer left right hCoarse hLeftSupport s hsX a)]
    exact hYSurvives s hsX a
  · rw [← Fintype.card_congr
      (xToZFiberEquiv outer left right hCoarse hLeftSupport s hsY a)]
    exact hXSurvives s hsY a

end MME.DWZStep1Support

open MME MME.DWZStep1Support

/-- Source-level form of Step 1 boundary reflection: pointwise nonzero fine
blocks of the literal CW square provide the support equation used above.  The
coarse shape is written out in the statement so the theorem has no hidden
certificate interface. -/
theorem solution
    {K : Type*} [Field K] (q m : ℕ)
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
          MME.DWZTable2Counts.split s a * m) :
    ∀ (s : Fin 15),
      MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position // outer t = s ∧ left 2 t = a} =
          MME.DWZTable2Counts.split s a * m := by
  have hs := fine_block_support_equations (K := K) q left right hFineSupport
  apply table2_step1_boundary_z_histogram m outer left right
  · intro i t
    simpa [table2Shape] using hCoarse i t
  · exact hs.1
  · exact hXSurvives
  · exact hYSurvives
