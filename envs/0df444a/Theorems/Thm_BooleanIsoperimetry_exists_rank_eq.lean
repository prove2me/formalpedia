-- Prove2me | Theorems.Thm_BooleanIsoperimetry_exists_rank_eq
-- name    : BooleanIsoperimetry.exists_rank_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:50.81817+00:00
-- url     : https://prove2.me/theorems/20d42958-6d79-4f18-bb4b-23e13d55d149
-- title:
--   Boolean Isoperimetry: exists rank eq
-- statement:
--   Every rank below `2 ^ n` is realised by some vertex of the `n`-cube
--   (`rank` is a bijection onto `range (2 ^ n)`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L254-L258
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L254-L258

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.exists_rank_eq {n j : ℕ} (hj : j < 2 ^ n) : ∃ w : Cube n, rank w = j := by sorry
