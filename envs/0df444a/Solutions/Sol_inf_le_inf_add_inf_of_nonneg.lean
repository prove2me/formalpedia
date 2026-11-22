-- Prove2me | solution 1 for inf_le_inf_add_inf_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:38.529386+00:00
-- url     : https://prove2.me/submissions/75e57eb5-cd25-4455-a934-7f193f1bcad4

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
public import Theorems.Thm_sub_inf_eq_posPart

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
variable (x : X)
theorem _root_.solution (a b : X) (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    x ⊓ (a + b) ≤ x ⊓ a + x ⊓ b := by
  set c := x ⊓ (a + b) with hc_def
  have hcx : c ≤ x := inf_le_left
  have hcab : c ≤ a + b := inf_le_right
  have hca_nn : 0 ≤ c ⊓ a := le_inf (le_inf hx (add_nonneg ha hb)) ha
  have h1 : c - c ⊓ a = (c - a)⁺ := sub_inf_eq_posPart c a
  have h2 : (c - a)⁺ ≤ b := by
    rw [← posPart_of_nonneg hb]
    exact posPart_mono (sub_le_iff_le_add.mpr (by rwa [add_comm]))
  have h3 : c - c ⊓ a ≤ x := by
    have := sub_le_self c hca_nn
    exact this.trans hcx
  have h4 : c - c ⊓ a ≤ x ⊓ b := le_inf h3 (h1 ▸ h2)
  have h5 : c ⊓ a ≤ x ⊓ a := inf_le_inf_right _ hcx
  have h4' : c ≤ x ⊓ b + c ⊓ a := sub_le_iff_le_add.mp h4
  calc c ≤ x ⊓ b + c ⊓ a := h4'
    _ ≤ x ⊓ b + x ⊓ a := by gcongr
    _ = x ⊓ a + x ⊓ b := add_comm _ _
