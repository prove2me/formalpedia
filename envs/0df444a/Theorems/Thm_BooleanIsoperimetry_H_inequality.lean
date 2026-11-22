-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_inequality
-- name    : BooleanIsoperimetry.H_inequality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:57.754448+00:00
-- url     : https://prove2.me/theorems/ac456190-efbb-4df1-8105-a84ea76a15c9
-- title:
--   Boolean Isoperimetry: H inequality
-- statement:
--   The Boolean Isoperimetry construction uses the H inequality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2117-L2120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2117-L2120

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

theorem BooleanIsoperimetry.H_inequality (n a b : ℕ) (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) :
    H (n + 1) (a + b) ≤ max (H n a) b + max (H n b) a := by sorry
