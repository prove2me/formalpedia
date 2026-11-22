-- Prove2me | Theorems.Thm_CriticalPortraits_bReach_sameFiber
-- name    : CriticalPortraits.bReach_sameFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:00.948227+00:00
-- url     : https://prove2.me/theorems/b301ba2d-4d79-4b92-b923-64b9ead8e53b
-- title:
--   Critical Portraits: b Reach same Fiber
-- statement:
--   Reachability preserves the fiber.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L390-L396
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L390-L396

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

theorem CriticalPortraits.bReach_sameFiber {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcanon : LevelCanonical d m U) {a b : ZMod (d * m)} (h : bReach U a b) :
    a.val % m = b.val % m := by sorry
