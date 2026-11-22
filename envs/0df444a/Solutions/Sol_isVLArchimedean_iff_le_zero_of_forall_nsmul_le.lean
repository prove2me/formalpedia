-- Prove2me | solution 1 for isVLArchimedean_iff_le_zero_of_forall_nsmul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:04.748047+00:00
-- url     : https://prove2.me/submissions/685017d4-e0e6-45e4-b324-bfa55bce733e

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
omit [VectorLattice X]
theorem _root_.solution :
    IsVLArchimedean X ↔ ∀ {x y : X}, (∀ n : ℕ, n • x ≤ y) → x ≤ 0 := by
  exact ⟨fun hArch _ _ h => hArch.le_zero_of_forall_nsmul_le h,
    fun H => ⟨fun {x y} h => H h⟩⟩
