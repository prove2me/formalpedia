-- Prove2me | Theorems.Thm_CriticalPortraits_hostSet_eq_of_mem_eraseMin
-- name    : CriticalPortraits.hostSet_eq_of_mem_eraseMin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:31.542392+00:00
-- url     : https://prove2.me/theorems/f2776030-60c9-4f47-93e3-4f15cd881192
-- title:
--   Critical Portraits: host Set eq of mem erase Min
-- statement:
--   Each block of a portrait is the host set of any of its survivors.  More precisely: if
--       `x ∈ eraseMin S` and `S ∈ P` then `hostSet P x = S` (the survivor's recovered home is its
--       block, by portrait disjointness).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L431-L441
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L431-L441

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
public import Theorems.Thm_CriticalPortraits_mem_T

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.hostSet_eq_of_mem_eraseMin {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {S : Finset (ZMod (d * m))} (hS : S ∈ P) {x : ZMod (d * m)} (hxe : x ∈ eraseMin S) :
    hostSet P x (mem_T.mpr ⟨S, hS, hxe⟩) = S := by sorry
