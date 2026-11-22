-- Prove2me | Theorems.Thm_CriticalPortraits_bAdj_symm
-- name    : CriticalPortraits.bAdj_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:57.896495+00:00
-- url     : https://prove2.me/theorems/b5159133-64f5-4ed0-8b0c-9048f9610f75
-- title:
--   Critical Portraits: b Adj symm
-- statement:
--   The Critical Portraits construction uses the b Adj symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L322-L325
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L322-L325

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

theorem CriticalPortraits.bAdj_symm {U : Finset (ZMod (d * m))} {a b : ZMod (d * m)} (h : bAdj U a b) : bAdj U b a := by sorry
