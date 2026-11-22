-- Prove2me | solution 1 for isGLB_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:34.366278+00:00
-- url     : https://prove2.me/submissions/46db38e2-2edf-4555-a812-22183cbb55b5

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
variable (x : X)
omit [AddCommGroup X] [IsOrderedAddMonoid X]
theorem _root_.solution {A B : Set X} {a b : X}
    (hA : IsGLB A a) (hB : IsGLB B b) : IsGLB (A ∪ B) (a ⊓ b) := by
  refine ⟨?_, ?_⟩
  · rintro z (hz | hz)
    · exact inf_le_left.trans (hA.1 hz)
    · exact inf_le_right.trans (hB.1 hz)
  · intro u hu
    have ha : u ≤ a := hA.2 fun z hz => hu (Or.inl hz)
    have hb : u ≤ b := hB.2 fun z hz => hu (Or.inr hz)
    exact le_inf ha hb
