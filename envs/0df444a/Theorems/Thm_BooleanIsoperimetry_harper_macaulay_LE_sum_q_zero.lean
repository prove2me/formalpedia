-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_macaulay_LE_sum_q_zero
-- name    : BooleanIsoperimetry.harper_macaulay_LE_sum_q_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:10.068807+00:00
-- url     : https://prove2.me/theorems/52f31e20-bcee-471d-9747-a99cf13d3a55
-- title:
--   Boolean Isoperimetry: harper macaulay LE sum q zero
-- statement:
--   Degenerate `q = 0` branch of the Case-I Macaulay sum leaf.  This removes
--   the non-positive canonical split from the Frankl–Füredi/Macaulay core: a
--   canonical split with `q = 0` has total mass at most one, so the inequality is a
--   finite `0/1` calculation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L615-L630
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L615-L630

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

theorem BooleanIsoperimetry.harper_macaulay_LE_sum_q_zero (n : ℕ)
    {a b p : ℕ}
    (hcasc : CascadeSplit (n + 1) (a + b) p 0)
    (hba : b ≤ a) :
    H (n + 1) p + H (n + 1) 0 ≤ H (n + 1) a + H (n + 1) b := by sorry
