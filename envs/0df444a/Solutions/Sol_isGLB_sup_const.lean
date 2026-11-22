-- Prove2me | solution 1 for isGLB_sup_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:46.531515+00:00
-- url     : https://prove2.me/submissions/ed115017-efde-4e71-acc7-9750cc5c97be

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
public import Theorems.Thm_sup_eq_add_posPart

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
variable (x : X)
theorem _root_.solution {A : Set X} {a : X} (x : X) (h : IsGLB A a) :
    IsGLB ((fun z => x ⊔ z) '' A) (x ⊔ a) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact sup_le_sup_left (h.1 hz) x
  · intro u hu
    have hA : ∀ z ∈ A, u - (x - a)⁺ ≤ z := by
      intro z hz
      have hzu : u ≤ z + (x - z)⁺ := by
        rw [← sup_eq_add_posPart, sup_comm]; exact hu ⟨z, hz, rfl⟩
      have hmono : (x - z)⁺ ≤ (x - a)⁺ := posPart_mono (sub_le_sub_left (h.1 hz) x)
      exact sub_le_iff_le_add.mpr (hzu.trans (by gcongr))
    have key : u - (x - a)⁺ ≤ a := h.2 hA
    calc u = (u - (x - a)⁺) + (x - a)⁺ := by abel
      _ ≤ a + (x - a)⁺ := by gcongr
      _ = a ⊔ x := (sup_eq_add_posPart a x).symm
      _ = x ⊔ a := sup_comm _ _
