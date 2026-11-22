-- Prove2me | Theorems.Thm_CriticalPortraits_reach_symm
-- name    : CriticalPortraits.reach_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:06.404721+00:00
-- url     : https://prove2.me/theorems/0a7dda9e-63ee-4319-a99f-6b2d4fd866f3
-- title:
--   Critical Portraits: reach symm
-- statement:
--   The Critical Portraits construction uses the reach symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L871-L876
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L871-L876

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.reach_symm [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))}
    {u v : ZMod (d * m)} (h : Relation.ReflTransGen (edgeStep P) u v) :
    Relation.ReflTransGen (edgeStep P) v u := by sorry
