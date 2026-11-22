-- Prove2me | Theorems.Thm_CriticalPortraits_mem_eraseMin
-- name    : CriticalPortraits.mem_eraseMin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:31.406453+00:00
-- url     : https://prove2.me/theorems/2f2e7118-8d5e-4fd8-84b5-436faef59ef1
-- title:
--   Critical Portraits: mem erase Min
-- statement:
--   Membership in `eraseMin`: everything of `S` except its `.val`-minimum (nonempty `S`).
--       The clean characterization the downstream membership reasoning will use.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L189-L193
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L189-L193

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

theorem CriticalPortraits.mem_eraseMin {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) (x : ZMod N) :
    x ∈ eraseMin S ↔ x ∈ S ∧ x ≠ minVal S h := by sorry
