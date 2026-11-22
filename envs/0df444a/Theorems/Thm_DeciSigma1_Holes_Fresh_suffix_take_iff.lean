-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_take_iff
-- name    : DeciSigma1.Holes.Fresh.suffix_take_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:29.287799+00:00
-- url     : https://prove2.me/theorems/1871f142-66b4-4638-b9b5-759cc4e1314d
-- title:
--   Fresh: suffix take iff
-- statement:
--   `u` ends at the cut `e ≤ |x|` of `x` iff it occurs at position `e - |u|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L72-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L72-L88

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable {x u v : List α}

theorem DeciSigma1.Holes.Fresh.suffix_take_iff {e : ℕ} (he : e ≤ x.length) :
    u <:+ x.take e ↔ u.length ≤ e ∧ u <+: x.drop (e - u.length) := by sorry
