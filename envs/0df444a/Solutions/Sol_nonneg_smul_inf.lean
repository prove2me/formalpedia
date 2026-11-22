-- Prove2me | solution 1 for nonneg_smul_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:33.956893+00:00
-- url     : https://prove2.me/submissions/f9d82e46-196c-4872-aa23-34fa11634664

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
public import Theorems.Thm_nonneg_smul_sup

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (x y : X)
theorem _root_.solution (a : ℝ) (nonneg : a ≥ 0) :
  a • (x ⊓ y) = (a • x) ⊓ (a • y) := by
    calc
      a • (x ⊓ y) = (-1) • a • (- (x ⊓ y)) := by simp
                _ = (-1) • a • ((-x) ⊔ (-y)) := by rw [neg_inf]
                _ = (-1) • ((a • -x) ⊔ (a • -y)) := by rw [nonneg_smul_sup (-x) (-y) a nonneg]
                _ = - ((-a • x) ⊔ (-a • y)) := by simp
                _ = (a • x) ⊓ (a • y) := by rw [neg_sup]; simp
