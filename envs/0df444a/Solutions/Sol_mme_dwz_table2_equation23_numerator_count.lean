-- Prove2me | solution 1 for mme_dwz_table2_equation23_numerator_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T13:29:24.224502+00:00
-- url     : https://prove2.me/submissions/857c69c5-483e-4bad-8957-3119bdd95ae6

import Definitions.Def_mme_dwz_table2_split_assignments
import Theorems.Thm_mme_dwz_table2_integer_counts_exact
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

open MME.DWZTable2Cardinality

private theorem prescribed_fiber_card_multinomial
    {Position Label : Type*}
    [Fintype Position] [DecidableEq Position]
    [Fintype Label] [DecidableEq Label]
    (counts : Label → ℕ)
    (hsum : ∑ i, counts i = Fintype.card Position) :
    Nat.card
        {f : Position → Label //
          ∀ i, Fintype.card {t : Position // f t = i} = counts i} =
      Nat.multinomial Finset.univ counts := by
  classical
  have h := mme_fintype_prescribed_fiber_function_card counts hsum
  calc
    Nat.card
        {f : Position → Label //
          ∀ i, Fintype.card {t : Position // f t = i} = counts i} =
        Fintype.card
          {f : Position → Label //
            ∀ i, Fintype.card {t : Position // f t = i} = counts i} :=
      Nat.card_eq_fintype_card
    _ = (Fintype.card Position).factorial /
          ∏ i, (counts i).factorial := by
      convert h using 1
    _ = Nat.multinomial Finset.univ counts := by
      simp only [Nat.multinomial, hsum]

private theorem cell_count_sum (m : ℕ) (r : SplitRegion) :
    (∑ i, cellCount m r i) = Fintype.card (RegionPosition m r) := by
  rcases mme_dwz_table2_integer_counts_exact with
    ⟨_, _, hsplit, _, _, _, hplus, _⟩
  cases r with
  | inl s =>
      simp only [cellCount, RegionPosition, regionSize]
      rw [← Finset.sum_mul, hsplit]
      exact (Fintype.card_fin _).symm
  | inr k =>
      simp only [cellCount, RegionPosition, regionSize]
      rw [← Finset.sum_mul, hplus]
      exact (Fintype.card_fin _).symm

private theorem local_split_assignment_card (m : ℕ) (r : SplitRegion) :
    Nat.card (LocalSplitAssignment m r) =
      Nat.multinomial Finset.univ (cellCount m r) := by
  simpa only [LocalSplitAssignment] using
    prescribed_fiber_card_multinomial
      (cellCount m r) (cell_count_sum m r)

private theorem boundary_product_eq_if (m : ℕ) :
    (∏ s : BoundaryShape,
      Nat.multinomial Finset.univ
        (fun r => MME.DWZTable2Counts.split s.1 r * m)) =
      ∏ s : Fin 15,
        if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
          Nat.multinomial Finset.univ
            (fun r => MME.DWZTable2Counts.split s r * m)
        else 1 := by
  classical
  let boundary : Fin 15 → Prop := fun s =>
    MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0
  let f : Fin 15 → ℕ := fun s => Nat.multinomial Finset.univ
    (fun r => MME.DWZTable2Counts.split s r * m)
  change (∏ s : {s : Fin 15 // boundary s}, f s.1) =
    ∏ s : Fin 15, if boundary s then f s else 1
  calc
    (∏ s : {s : Fin 15 // boundary s}, f s.1) =
        ∏ s ∈ Finset.univ.filter boundary, f s := by
          symm
          exact Finset.prod_subtype (Finset.univ.filter boundary)
            (by simp) f
    _ = ∏ s : Fin 15, if boundary s then f s else 1 := by
      exact Finset.prod_filter boundary f

theorem solution (m : ℕ) :
    Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) =
      (∏ s : Fin 15,
        if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
          Nat.multinomial Finset.univ
            (fun r => MME.DWZTable2Counts.split s r * m)
        else 1) *
      ∏ k : Fin 5,
        Nat.multinomial Finset.univ
          (fun r => MME.DWZTable2Counts.plusSplit k r * m) := by
  classical
  let (r : SplitRegion) := Fintype.ofFinite (LocalSplitAssignment m r)
  calc
    Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) =
        ∏ r : SplitRegion, Nat.card (LocalSplitAssignment m r) := by
      unfold SplitAssignments
      rw [Nat.card_eq_fintype_card, Fintype.card_pi]
      apply Finset.prod_congr rfl
      intro r hr
      rw [Nat.card_eq_fintype_card]
    _ = ∏ r : SplitRegion,
        Nat.multinomial Finset.univ (cellCount m r) := by
      apply Finset.prod_congr rfl
      intro r hr
      exact local_split_assignment_card m r
    _ = (∏ s : BoundaryShape,
          Nat.multinomial Finset.univ
            (fun i => MME.DWZTable2Counts.split s.1 i * m)) *
        ∏ k : Fin 5,
          Nat.multinomial Finset.univ
            (fun i => MME.DWZTable2Counts.plusSplit k i * m) := by
      rw [Fintype.prod_sum_type]
      rfl
    _ = _ := by
      rw [boundary_product_eq_if]
