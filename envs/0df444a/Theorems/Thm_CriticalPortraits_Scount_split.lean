-- Prove2me | Theorems.Thm_CriticalPortraits_Scount_split
-- name    : CriticalPortraits.Scount_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:25.413686+00:00
-- url     : https://prove2.me/theorems/8acb2b1a-3140-41ca-b54c-bc54558fd48e
-- title:
--   Critical Portraits: Scount split
-- statement:
--   **Scount split** through an interior `U`-point `w`: if `x < w.val < y` and `w ∈ U`, then
--       `Scount U x y = Scount U x w.val + 1 + Scount U w.val y`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L402-L440
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L402-L440

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

theorem CriticalPortraits.Scount_split {d m : ℕ} [NeZero (d * m)] {U : Finset (ZMod (d * m))} {x y : ℕ}
    {w : ZMod (d * m)}
    (hwU : w ∈ U) (hxw : x < w.val) (hwy : w.val < y) :
    Scount U x y = Scount U x w.val + 1 + Scount U w.val y := by sorry
