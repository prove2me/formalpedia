-- Prove2me | solution 1 for isGLB_sup_sets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:33.813585+00:00
-- url     : https://prove2.me/submissions/c93a51fa-0e0e-4d37-bc22-81da208fa5b7

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
public import Theorems.Thm_isGLB_sup_const

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
variable (x : X)
theorem _root_.solution {A B : Set X} {a b : X}
    (hA : IsGLB A a) (hB : IsGLB B b) :
    IsGLB ((fun p : X × X => p.1 ⊔ p.2) '' (A ×ˢ B)) (a ⊔ b) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨⟨p, q⟩, ⟨hp, hq⟩, rfl⟩
    exact sup_le_sup (hA.1 hp) (hB.1 hq)
  · intro u hu
    have h1 : ∀ q ∈ B, u ≤ a ⊔ q := by
      intro q hq
      have hlb : u ∈ lowerBounds ((fun z => q ⊔ z) '' A) := by
        rintro _ ⟨p, hp, rfl⟩
        have hpq : u ≤ p ⊔ q := hu ⟨(p, q), ⟨hp, hq⟩, rfl⟩
        rw [sup_comm] at hpq; exact hpq
      have hqa : u ≤ q ⊔ a := (isGLB_sup_const q hA).2 hlb
      rwa [sup_comm] at hqa
    exact (isGLB_sup_const a hB).2 (by rintro _ ⟨q, hq, rfl⟩; exact h1 q hq)
