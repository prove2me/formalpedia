-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_take_occ
-- name    : DeciSigma1.Holes.Fresh.take_occ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:41.001803+00:00
-- url     : https://prove2.me/theorems/799f4459-afe7-4df1-a248-df06f332f404
-- title:
--   Fresh: take occ
-- statement:
--   The cut `i + |u|` after an occurrence at `i`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L103-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L103-L104

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

theorem DeciSigma1.Holes.Fresh.take_occ {i : ℕ} (hu : u <+: x.drop i) : x.take (i + u.length) = x.take i ++ u := by sorry
