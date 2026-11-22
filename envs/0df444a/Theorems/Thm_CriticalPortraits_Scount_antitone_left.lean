-- Prove2me | Theorems.Thm_CriticalPortraits_Scount_antitone_left
-- name    : CriticalPortraits.Scount_antitone_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:06.503338+00:00
-- url     : https://prove2.me/theorems/2b61fb96-c1f8-432b-a295-1942d4daa939
-- title:
--   Critical Portraits: Scount antitone left
-- statement:
--   Enlarging the lower endpoint shrinks the open interval: `Scount` is antitone in `x`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L95-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L95-L101

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

theorem CriticalPortraits.Scount_antitone_left {d m : ℕ} (U : Finset (ZMod (d * m))) {x x' y : ℕ}
    (hxx : x ≤ x') : Scount U x' y ≤ Scount U x y := by sorry
