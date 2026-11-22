-- Prove2me | Theorems.Thm_CriticalPortraits_hiV_lt_d
-- name    : CriticalPortraits.hiV_lt_d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:38.144412+00:00
-- url     : https://prove2.me/theorems/e2479735-344c-4189-bee5-f35e2e546b13
-- title:
--   Critical Portraits: hi V lt d
-- statement:
--   Every survivor's level is `< d` (hence `hiV x ≤ d - 1`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L475-L479
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L475-L479

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

theorem CriticalPortraits.hiV_lt_d [NeZero (d * m)] (_hm : 0 < m) (x : ZMod (d * m)) : hiV x < d := by sorry
