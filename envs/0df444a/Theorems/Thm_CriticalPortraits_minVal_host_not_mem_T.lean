-- Prove2me | Theorems.Thm_CriticalPortraits_minVal_host_not_mem_T
-- name    : CriticalPortraits.minVal_host_not_mem_T
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:16.582367+00:00
-- url     : https://prove2.me/theorems/894e1091-ed76-4152-8d33-0ff8ef37c2c9
-- title:
--   Critical Portraits: min Val host not mem T
-- statement:
--   The dropped point of a block is not a survivor of `P` (blocks are disjoint).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L846-L860
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L846-L860

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

theorem CriticalPortraits.minVal_host_not_mem_T {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x : ZMod (d * m)} (hx : x ∈ T P) (hne : (hostSet P x hx).Nonempty) :
    minVal (hostSet P x hx) hne ∉ T P := by sorry
