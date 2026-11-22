-- Prove2me | Theorems.Thm_BooleanIsoperimetry_HIncrement_le_of_mem_layer
-- name    : BooleanIsoperimetry.HIncrement_le_of_mem_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:05.762599+00:00
-- url     : https://prove2.me/theorems/e3a157c1-24e4-4b48-b639-3d7d3ae0dd08
-- title:
--   Boolean Isoperimetry: HIncrement le of mem layer
-- statement:
--   **Per-layer increment upper bound.**  For a rank `j` in Macaulay layer `r`
--   (i.e. `binomPrefix n r ≤ j < binomPrefix n (r+1)`, the cardinality-`r` band), the
--   increment `HIncrement n j` (the min coordinate of the rank-`j` vertex) is at most
--   `n - r`.  This is the upper companion of `HIncrement_lower`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L264-L278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L264-L278

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

theorem BooleanIsoperimetry.HIncrement_le_of_mem_layer {n r j : ℕ} (hr : 1 ≤ r)
    (hlo : binomPrefix n r ≤ j) (hhi : j < binomPrefix n (r + 1)) :
    HIncrement n j ≤ n - r := by sorry
