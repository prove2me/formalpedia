-- Prove2me | solution 1 for mme_dwz_table2_boundary_interior_implies_grouped_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:58:33.145487+00:00
-- url     : https://prove2.me/submissions/293fcf60-36b6-4c81-b01b-c81f938473de

import Definitions.Def_mme_dwz_table2_step1_z_histogram_fibers

namespace MME.DWZStep1Histogram

open MME

set_option autoImplicit false
set_option warningAsError true

private def regionOfShape :
    Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s =>
  if h : MME.DWZSquare.shapeX s = 0 ∨
      MME.DWZSquare.shapeY s = 0 then
    Sum.inl ⟨s, h⟩
  else
    Sum.inr (MME.DWZSquare.shapeZ s)

private def boundaryRegionFiberEquiv
    {Position : Type*}
    (outer : Position → Fin 15) (zLeft : Position → Fin 3)
    (s : MME.DWZTable2Cardinality.BoundaryShape) (a : Fin 3) :
    {t : Position //
      regionOfShape (outer t) = Sum.inl s ∧ zLeft t = a} ≃
      ComponentZFiber outer zLeft s.1 a where
  toFun t := ⟨t.1, by
    have hb : MME.DWZSquare.shapeX (outer t.1) = 0 ∨
        MME.DWZSquare.shapeY (outer t.1) = 0 := by
      by_contra hn
      have he := t.2.1
      rw [regionOfShape, dif_neg hn] at he
      cases he
    have he :
        (⟨outer t.1, hb⟩ : MME.DWZTable2Cardinality.BoundaryShape) = s := by
      have hsum := t.2.1
      rw [regionOfShape, dif_pos hb] at hsum
      exact Sum.inl.inj hsum
    exact ⟨congrArg Subtype.val he, t.2.2⟩⟩
  invFun t := ⟨t.1, by
    have hb : MME.DWZSquare.shapeX (outer t.1) = 0 ∨
        MME.DWZSquare.shapeY (outer t.1) = 0 := by
      rw [t.2.1]
      exact s.2
    constructor
    · rw [regionOfShape, dif_pos hb]
      apply congrArg Sum.inl
      apply Subtype.ext
      exact t.2.1
    · exact t.2.2⟩
  left_inv t := by
    apply Subtype.ext
    rfl
  right_inv t := by
    apply Subtype.ext
    rfl

private def interiorRegionFiberEquiv
    {Position : Type*}
    (outer : Position → Fin 15) (zLeft : Position → Fin 3)
    (k : Fin 5) (a : Fin 3) :
    {t : Position //
      regionOfShape (outer t) = Sum.inr k ∧ zLeft t = a} ≃
      InteriorZFiber outer zLeft k a where
  toFun t := by
    have hnot : ¬ (MME.DWZSquare.shapeX (outer t.1) = 0 ∨
        MME.DWZSquare.shapeY (outer t.1) = 0) := by
      by_contra hb
      have he := t.2.1
      rw [regionOfShape, dif_pos hb] at he
      cases he
    have hn : MME.DWZSquare.shapeX (outer t.1) ≠ 0 ∧
        MME.DWZSquare.shapeY (outer t.1) ≠ 0 := by
      push Not at hnot
      exact hnot
    have hz : MME.DWZSquare.shapeZ (outer t.1) = k := by
      have he := t.2.1
      rw [regionOfShape, dif_neg (by simpa using hn)] at he
      exact Sum.inr.inj he
    exact ⟨t.1, hz, hn.1, hn.2, t.2.2⟩
  invFun t := ⟨t.1, by
    have hn : ¬ (MME.DWZSquare.shapeX (outer t.1) = 0 ∨
        MME.DWZSquare.shapeY (outer t.1) = 0) := by
      push Not
      exact ⟨t.2.2.1, t.2.2.2.1⟩
    exact ⟨by
      rw [regionOfShape, dif_neg hn]
      exact congrArg Sum.inr t.2.1, t.2.2.2.2⟩⟩
  left_inv t := by
    apply Subtype.ext
    rfl
  right_inv t := by
    apply Subtype.ext
    rfl

end MME.DWZStep1Histogram

open MME MME.DWZStep1Histogram

/-- Exact boundary and interior Z histograms are precisely the grouped
compatibility-cell counts used after DWZ Additional Zeroing-Out Step 1. -/
theorem solution
    (m : ℕ)
    {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15) (zLeft : Position → Fin 3)
    (hBoundary : ∀ (s : Fin 15),
      MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card (ComponentZFiber outer zLeft s a) =
          MME.DWZTable2Counts.split s a * m)
    (hInterior : ∀ (k : Fin 5) (a : Fin 3),
      Fintype.card (InteriorZFiber outer zLeft k a) =
        MME.DWZTable2Counts.plusSplit k a * m) :
    let groupedRegion :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s =>
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
      Fintype.card
          {t : Position // groupedRegion (outer t) = r ∧ zLeft t = a} =
        MME.DWZTable2Cardinality.cellCount m r a := by
  change ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
    Fintype.card
        {t : Position // regionOfShape (outer t) = r ∧ zLeft t = a} =
      MME.DWZTable2Cardinality.cellCount m r a
  intro r a
  rcases r with s | k
  · rw [Fintype.card_congr (boundaryRegionFiberEquiv outer zLeft s a)]
    exact hBoundary s.1 s.2 a
  · rw [Fintype.card_congr (interiorRegionFiberEquiv outer zLeft k a)]
    exact hInterior k a
