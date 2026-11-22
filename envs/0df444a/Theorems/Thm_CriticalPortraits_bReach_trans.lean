-- Prove2me | Theorems.Thm_CriticalPortraits_bReach_trans
-- name    : CriticalPortraits.bReach_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:57.996498+00:00
-- url     : https://prove2.me/theorems/e29d14f3-8146-466c-893d-ad325850dc7a
-- title:
--   Critical Portraits: b Reach trans
-- statement:
--   The Critical Portraits construction uses the b Reach trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L341-L343
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L341-L343

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

theorem CriticalPortraits.bReach_trans {U : Finset (ZMod (d * m))} {a b c : ZMod (d * m)}
    (h1 : bReach U a b) (h2 : bReach U b c) : bReach U a c := by sorry
