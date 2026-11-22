-- Prove2me | solution 1 for sup_smul_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:38.867793+00:00
-- url     : https://prove2.me/submissions/069f13cf-f26d-4a77-9238-3ab3324bdabb

module
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (x y : X)
theorem _root_.solution (a b : ℝ) (h : 0 ≤ x) :
    (a ⊔ b) • x = (a • x) ⊔ (b • x) := by
  apply le_antisymm
  · cases max_choice a b with
      | inl h => rw [h]; exact le_sup_left
      | inr h => rw [h]; exact le_sup_right
  · apply sup_le
    · exact smul_le_smul_of_nonneg_right le_sup_left h
    · exact smul_le_smul_of_nonneg_right le_sup_right h
