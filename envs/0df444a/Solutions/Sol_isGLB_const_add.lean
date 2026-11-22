-- Prove2me | solution 1 for isGLB_const_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:29.671822+00:00
-- url     : https://prove2.me/submissions/3d2cc799-bca6-46a3-85f9-503ea3f1e812

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
theorem _root_.solution {A : Set X} {a : X} (x : X) (h : IsGLB A a) :
    IsGLB ((fun z => x + z) '' A) (x + a) :=
  (OrderIso.addLeft x).isGLB_image'.mpr h
