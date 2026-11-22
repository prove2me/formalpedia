-- Prove2me | solution 1 for isLUB_inf_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:45.74626+00:00
-- url     : https://prove2.me/submissions/b9db2d6b-2b87-4738-b072-a0fff1651241

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
public import Theorems.Thm_inf_eq_sub_posPart

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
variable (x : X)
theorem _root_.solution {A : Set X} {a : X} (x : X) (h : IsLUB A a) :
    IsLUB ((fun z => x ⊓ z) '' A) (x ⊓ a) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact inf_le_inf_left x (h.1 hz)
  · intro u hu
    have hA : ∀ z ∈ A, z ≤ u + (a - x)⁺ := by
      intro z hz
      have hzu : z - (z - x)⁺ ≤ u := by
        rw [← inf_eq_sub_posPart, inf_comm]; exact hu ⟨z, hz, rfl⟩
      have hmono : (z - x)⁺ ≤ (a - x)⁺ := posPart_mono (sub_le_sub_right (h.1 hz) x)
      have h1 : z ≤ u + (z - x)⁺ := sub_le_iff_le_add.mp hzu
      exact h1.trans (by gcongr)
    have key : a ≤ u + (a - x)⁺ := h.2 hA
    calc x ⊓ a = a ⊓ x := inf_comm _ _
      _ = a - (a - x)⁺ := inf_eq_sub_posPart a x
      _ ≤ u := sub_le_iff_le_add.mpr key
