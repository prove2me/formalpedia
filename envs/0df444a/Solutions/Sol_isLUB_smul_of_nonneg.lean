-- Prove2me | solution 1 for isLUB_smul_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:35.089885+00:00
-- url     : https://prove2.me/submissions/dc890359-531e-4674-9258-e4483df5b6c8

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
theorem _root_.solution {A : Set X} {a : X} {lam : ℝ} (hlam : 0 ≤ lam)
    (h : IsLUB A a) : IsLUB ((fun z => lam • z) '' A) (lam • a) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact smul_le_smul_of_nonneg_left (h.1 hz) hlam
  · intro u hu
    by_cases hl : lam = 0
    · subst hl; rw [zero_smul]
      rcases A.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
      · have hmin : ∀ b : X, a ≤ b := fun b =>
          h.2 fun x hx => (Set.notMem_empty x hx).elim
        have h0a : 0 ≤ a :=
          (add_le_add_iff_left a).mp (by rw [add_zero]; exact hmin (a + a))
        exact h0a.trans (hmin u)
      · have : (0 : ℝ) • z ≤ u := hu ⟨z, hz, rfl⟩
        rwa [zero_smul] at this
    · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hl)
      have hinv_nn : 0 ≤ lam⁻¹ := le_of_lt (inv_pos.mpr hlam_pos)
      have h_ub : lam⁻¹ • u ∈ upperBounds A := fun z hz => by
        have h1 : lam⁻¹ • (lam • z) ≤ lam⁻¹ • u :=
          smul_le_smul_of_nonneg_left (hu ⟨z, hz, rfl⟩) hinv_nn
        rwa [inv_smul_smul₀ hl] at h1
      have h4 : lam • a ≤ lam • (lam⁻¹ • u) :=
        smul_le_smul_of_nonneg_left (h.2 h_ub) hlam
      rwa [smul_inv_smul₀ hl] at h4
