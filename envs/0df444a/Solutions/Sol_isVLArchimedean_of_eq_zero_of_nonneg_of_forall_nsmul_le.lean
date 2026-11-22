-- Prove2me | solution 1 for isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:03.966534+00:00
-- url     : https://prove2.me/submissions/f084bbda-4415-42a1-b5a1-ccbfe8a06057

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
section
@[expose] public section
section LatticeOrderedGroup
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
variable (x : X)
end LatticeOrderedGroup
section VectorLattice
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (x y : X)
section Archimedean
private lemma nsmul_posPart_le_of_forall_nsmul_le {Y : Type*} [AddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] (x : Y) :
    ∀ (n : ℕ) (v : Y), (∀ k : ℕ, k ≤ n → k • x ≤ v) → n • (x ⊔ 0) ≤ v := by
  intro n
  induction n with
  | zero =>
    intro v h
    simpa using h 0 (le_refl 0)
  | succ n ih =>
    intro v h
    rw [succ_nsmul, add_sup, add_zero]
    refine sup_le ?_ (ih v fun k hk => h k (hk.trans (Nat.le_succ n)))
    rw [← le_sub_iff_add_le]
    refine ih (v - x) fun k hk => ?_
    rw [le_sub_iff_add_le, ← succ_nsmul]
    exact h (k + 1) (Nat.succ_le_succ hk)
namespace IsVLArchimedean
end IsVLArchimedean
variable [IsVLArchimedean X]
end Archimedean
end VectorLattice
end
end

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (x y : X)
omit [VectorLattice X]
theorem _root_.solution
    (H : ∀ {x y : X}, 0 ≤ x → (∀ n : ℕ, n • x ≤ y) → x = 0) :
    IsVLArchimedean X := by
  refine ⟨fun {x y} h => ?_⟩
  have hsup : x ⊔ 0 = 0 :=
    H le_sup_right
      (fun n => nsmul_posPart_le_of_forall_nsmul_le x n y fun k _ => h k)
  exact sup_eq_right.mp hsup
