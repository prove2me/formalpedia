-- Prove2me | Theorems.Thm_CriticalPortraits_mem_T
-- name    : CriticalPortraits.mem_T
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:34.651263+00:00
-- url     : https://prove2.me/theorems/1f77599c-58f0-4737-853a-a714f5767e54
-- title:
--   Critical Portraits: mem T
-- statement:
--   Membership in `T P`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L305-L308
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L305-L308

module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators

theorem CriticalPortraits.mem_T {N : ℕ} {P : Finset (Finset (ZMod N))} {x : ZMod N} :
    x ∈ T P ↔ ∃ S ∈ P, x ∈ eraseMin S := by sorry
