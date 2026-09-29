-- Prove2me | solution 1 for mme_dwz_table2_useful_implies_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T21:10:14.987078+00:00
-- url     : https://prove2.me/submissions/4cca0572-3337-478b-89b7-c38e6312d38d

import Definitions.Def_mme_dwz_table2_split_assignments

open BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZTable2TensorHoleSemantics

open MME.DWZTable2Cardinality

/-- The region quotient used in the exact Table-2 compatibility predicate.
Boundary components stay separate; components with both first two degrees
positive are grouped by their coarse Z degree. -/
private def regionOfShape (s : Fin 15) : SplitRegion :=
  if h : MME.DWZSquare.shapeX s = 0 ∨
      MME.DWZSquare.shapeY s = 0 then
    Sum.inl ⟨s, h⟩
  else
    Sum.inr (MME.DWZSquare.shapeZ s)

/-- The integral Table-2 split counts push forward from individual
components to the boundary/interior region quotient.  This is the finite
Table-2 specialization of grouping the `(+,+,k)` components in the rewrite
from Definition 6.1 to the disjoint conditions used before Equation (23). -/
private theorem split_pushforward (r : SplitRegion) (a : Fin 3) :
    (∑ s : {s : Fin 15 // regionOfShape s = r},
      MME.DWZTable2Counts.split s.1 a) =
        MME.DWZTable2Cardinality.cellCount 1 r a := by
  classical
  fin_cases r <;> fin_cases a <;> decide

/-- Partition a region-and-split fiber by its exact Table-2 component. -/
private def usefulFiberEquiv
    {Position : Type*}
    (outer : Position → Fin 15)
    (small : Position → Fin 3 × Fin 3)
    (r : SplitRegion) (a : Fin 3) :
    (Σ s : {s : Fin 15 // regionOfShape s = r},
      {t : Position // outer t = s.1 ∧ (small t).1 = a}) ≃
      {t : Position //
        regionOfShape (outer t) = r ∧ (small t).1 = a} where
  toFun x :=
    ⟨x.2.1, by
      refine ⟨?_, x.2.2.2⟩
      rw [x.2.2.1, x.1.2]⟩
  invFun t :=
    ⟨⟨outer t.1, t.2.1⟩, ⟨t.1, rfl, t.2.2⟩⟩
  left_inv x := by
    rcases x with ⟨⟨s, hs⟩, ⟨t, ht, ha⟩⟩
    cases ht
    rfl
  right_inv t := by
    rcases t with ⟨t, ht, ha⟩
    rfl

end MME.DWZTable2TensorHoleSemantics

open MME.DWZTable2Cardinality
open MME.DWZTable2TensorHoleSemantics

/-- **DWZ Definition 6.3 implies Definition 6.1, in the exact Table-2
encoding.**

If a fine Z word has the prescribed split histogram separately on every
large component, as required for usefulness, then it satisfies the grouped
boundary/interior compatibility cells used by the finite Claim-6.8
formalization.  No compatibility conclusion is included in the premise: the
premise consists only of the fifteen by three component-level split counts. -/
theorem solution
    (m : ℕ)
    {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15)
    (small : Position → Fin 3 × Fin 3)
    (hUseful : ∀ (s : Fin 15) (a : Fin 3),
      Fintype.card
          {t : Position // outer t = s ∧ (small t).1 = a} =
        MME.DWZTable2Counts.split s a * m) :
    let regionOfShape :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
      Fintype.card
          {t : Position //
            regionOfShape (outer t) = r ∧ (small t).1 = a} =
        MME.DWZTable2Cardinality.cellCount m r a := by
  classical
  dsimp only
  intro r a
  change Fintype.card
      {t : Position //
        MME.DWZTable2TensorHoleSemantics.regionOfShape (outer t) = r ∧
          (small t).1 = a} =
    MME.DWZTable2Cardinality.cellCount m r a
  rw [← Fintype.card_congr (usefulFiberEquiv outer small r a),
    Fintype.card_sigma]
  simp_rw [hUseful]
  rw [← Finset.sum_mul, split_pushforward]
  cases r <;> simp [MME.DWZTable2Cardinality.cellCount]
