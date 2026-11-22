-- Prove2me | Theorems.Thm_CriticalPortraits_betaRoot_le
-- name    : CriticalPortraits.betaRoot_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:00.181188+00:00
-- url     : https://prove2.me/theorems/275c65ff-84d0-4539-b56d-fdb1b31053e5
-- title:
--   Critical Portraits: beta Root le
-- statement:
--   The root's `.val` is `≤ x.val`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L581-L592
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L581-L592

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

theorem CriticalPortraits.betaRoot_le {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) (x : ZMod (d * m)) :
    (betaRoot hd hm hcanon x).val ≤ x.val := by sorry
