-- Prove2me | Theorems.Thm_BooleanIsoperimetry_boundaryCostH_eq_H_add_slack
-- name    : BooleanIsoperimetry.boundaryCostH_eq_H_add_slack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:08.29399+00:00
-- url     : https://prove2.me/theorems/e22f2652-5615-4dc6-8aa6-3b6d95a31224
-- title:
--   Boolean Isoperimetry: boundary Cost H eq H add slack
-- statement:
--   Exact slack decomposition of the max-form boundary cost.  The two truncated
--   terms are precisely the slack that is needed in the GT regime, where the simpler
--   sum-form `H N a + H N b` is false.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L112-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L112-L116

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.boundaryCostH_eq_H_add_slack (N a b : ℕ) :
    boundaryCostH N a b =
      H N a + H N b + (b - H N a) + (a - H N b) := by sorry
