-- Prove2me | solution 1 for posPart_smul_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:34.903838+00:00
-- url     : https://prove2.me/submissions/20cdb147-7ee4-4ad4-a0c6-753e888d97e3

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
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) (x : X) :
    (a • x)⁺ = a • x⁺ := by
  change (a • x) ⊔ 0 = a • (x ⊔ 0)
  rw [← smul_zero a, ← nonneg_smul_sup x 0 a ha, smul_zero]
