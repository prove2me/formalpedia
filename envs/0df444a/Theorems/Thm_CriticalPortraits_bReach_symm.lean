-- Prove2me | Theorems.Thm_CriticalPortraits_bReach_symm
-- name    : CriticalPortraits.bReach_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:37.58479+00:00
-- url     : https://prove2.me/theorems/9964d4a9-2df9-4be3-8c60-905035893bce
-- title:
--   Critical Portraits: b Reach symm
-- statement:
--   The Critical Portraits construction uses the b Reach symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L334-L339
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L334-L339

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.bReach_symm {U : Finset (ZMod (d * m))} {a b : ZMod (d * m)} (h : bReach U a b) :
    bReach U b a := by sorry
