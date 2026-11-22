-- Prove2me | solution 1 for nonneg_smul_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:55.848981+00:00
-- url     : https://prove2.me/submissions/5432d99a-8e92-4b8a-ba06-b6b146b325b9

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
theorem _root_.solution (a : ℝ) (nonneg : a ≥ 0) :
  a • (x ⊔ y) = (a • x) ⊔ (a • y) := by
  by_cases h : a = 0
  · subst h
    simp only [zero_smul]; exact Eq.symm Std.max_self
  · apply le_antisymm
    · have hx : a⁻¹ • a • x ≤ a⁻¹ • (a • x ⊔ a • y) := by
        exact smul_le_smul_of_nonneg_left
         le_sup_left
         (by norm_num [nonneg])
      have hy : a⁻¹ • a • y ≤ a⁻¹ • (a • x ⊔ a • y) := by
        exact smul_le_smul_of_nonneg_left
         le_sup_right
         (by norm_num [nonneg])
      simp only [inv_smul_smul₀ h] at hx hy
      have hxy : x ⊔ y ≤ a⁻¹ • (a • x ⊔ a • y) :=
        sup_le hx hy
      calc
        a • (x ⊔ y) ≤ a • (a⁻¹ • (a • x ⊔ a • y)) := by
                      exact smul_le_smul_of_nonneg_left hxy nonneg
                  _ = a • x ⊔ a • y := by rw [smul_smul a a⁻¹ _]; norm_num [h];
    · have hx : a • x ≤ a • (x ⊔ y) :=
        smul_le_smul_of_nonneg_left le_sup_left nonneg
      have hy : a • y ≤ a • (x ⊔ y) :=
        smul_le_smul_of_nonneg_left le_sup_right nonneg
      exact sup_le hx hy
