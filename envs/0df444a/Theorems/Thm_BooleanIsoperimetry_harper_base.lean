-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_base
-- name    : BooleanIsoperimetry.harper_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:59.531812+00:00
-- url     : https://prove2.me/theorems/6b86208f-c2ec-436a-b3e4-a37ee2ebffe9
-- title:
--   Boolean Isoperimetry: harper base
-- statement:
--   The Boolean Isoperimetry construction uses the harper base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2166-L2170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2166-L2170

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

theorem BooleanIsoperimetry.harper_base (A : Finset (Cube 0)) (k : ℕ) (hk : A.card = k) :
    (neighborhood 1 (simplicialInitSeg 0 k)).card ≤ (neighborhood 1 A).card := by sorry
