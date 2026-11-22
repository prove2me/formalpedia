-- Prove2me | Theorems.Thm_BooleanIsoperimetry_boundaryCost_eq_case_le
-- name    : BooleanIsoperimetry.boundaryCost_eq_case_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:17.912093+00:00
-- url     : https://prove2.me/theorems/2ac94df6-eb6b-409e-8450-5ae7542c0235
-- title:
--   Boolean Isoperimetry: boundary Cost eq case le
-- statement:
--   The Boolean Isoperimetry construction uses the boundary Cost eq case le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L381-L388
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L381-L388

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

theorem BooleanIsoperimetry.boundaryCost_eq_case_le
    {n a b : ℕ} (ha : a ≤ 2 ^ n) (hb_le_a : b ≤ a) (hcase : a ≤ H n b) :
    max (H n a) b + max (H n b) a = H n a + H n b := by sorry
