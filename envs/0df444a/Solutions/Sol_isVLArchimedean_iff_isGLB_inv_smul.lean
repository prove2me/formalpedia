-- Prove2me | solution 1 for isVLArchimedean_iff_isGLB_inv_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:49.407324+00:00
-- url     : https://prove2.me/submissions/66e6e82b-25b4-407b-a93b-ffa420acdf8c

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
public import Theorems.Thm_isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le
public import Theorems.Thm_isVLArchimedean_iff_le_zero_of_forall_nsmul_le

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (x y : X)
theorem _root_.solution :
    IsVLArchimedean X ↔
      ∀ u : X, 0 ≤ u →
        IsGLB {v : X | ∃ n : ℕ, 0 < n ∧ v = (n : ℝ)⁻¹ • u} 0 := by
  constructor
  · intro hArch u hu
    refine ⟨?_, ?_⟩
    · rintro _ ⟨n, _, rfl⟩
      exact smul_nonneg (by positivity) hu
    · intro w hw
      apply isVLArchimedean_iff_le_zero_of_forall_nsmul_le.mp hArch (y := u)
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hnpos
      · simpa using hu
      · have hwn : w ≤ (n : ℝ)⁻¹ • u := hw ⟨n, hnpos, rfl⟩
        have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have h1 : (n : ℝ) • w ≤ (n : ℝ) • ((n : ℝ)⁻¹ • u) :=
          smul_le_smul_of_nonneg_left hwn hn_nn
        rw [smul_inv_smul₀ (Nat.cast_ne_zero.mpr hnpos.ne')] at h1
        rwa [Nat.cast_smul_eq_nsmul] at h1
  · intro H
    apply isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le
    intro x y hx h
    set u := y ⊔ 0 with hu_def
    have hu : 0 ≤ u := le_sup_right
    have hx_lb : x ∈ lowerBounds {v : X | ∃ n : ℕ, 0 < n ∧ v = (n : ℝ)⁻¹ • u} := by
      rintro _ ⟨n, hnpos, rfl⟩
      have h1 : (n : ℝ) • x ≤ u := by
        rw [Nat.cast_smul_eq_nsmul]
        exact (h n).trans le_sup_left
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
      have h2 : (n : ℝ)⁻¹ • ((n : ℝ) • x) ≤ (n : ℝ)⁻¹ • u :=
        smul_le_smul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hn_pos))
      rwa [inv_smul_smul₀ hn_pos.ne'] at h2
    exact le_antisymm ((H u hu).2 hx_lb) hx
