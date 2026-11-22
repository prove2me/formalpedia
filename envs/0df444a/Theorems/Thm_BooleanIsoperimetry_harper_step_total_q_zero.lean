-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_step_total_q_zero
-- name    : BooleanIsoperimetry.harper_step_total_q_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:39:20.152093+00:00
-- url     : https://prove2.me/theorems/10ebc46f-ed65-4b2f-9ebf-26ed2d9c3c2c
-- title:
--   Boolean Isoperimetry: harper step total q zero
-- statement:
--   The four-block prefix profile exposed by lowering a level-`n+1`
--   interleaving to the two level-`n` slices.  The first pair `(x0, y0)` is read
--   one layer ahead of the second pair `(x1, y1)`, matching the Pascal shift in
--   `CascadeInterleaves.lower_succ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L152-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L152-L164

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

theorem BooleanIsoperimetry.harper_step_total_q_zero (n : ℕ) {a b p : ℕ}
    (hcasc : CascadeSplit (n + 1) (a + b) p 0) :
    H (n + 2) (a + b) ≤ boundaryCostH (n + 1) a b := by sorry
