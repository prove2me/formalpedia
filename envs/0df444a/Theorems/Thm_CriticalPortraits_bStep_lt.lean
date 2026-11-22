-- Prove2me | Theorems.Thm_CriticalPortraits_bStep_lt
-- name    : CriticalPortraits.bStep_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:41.889295+00:00
-- url     : https://prove2.me/theorems/c8cde5f6-bfa6-4181-98d6-905ca452f607
-- title:
--   Critical Portraits: b Step lt
-- statement:
--   The step strictly decreases `.val` when `x ∈ U`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L542-L546
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L542-L546

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

theorem CriticalPortraits.bStep_lt {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x : ZMod (d * m)} (hx : x ∈ U) :
    (bStep U x).val < x.val := by sorry
