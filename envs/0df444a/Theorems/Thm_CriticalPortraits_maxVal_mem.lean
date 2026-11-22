-- Prove2me | Theorems.Thm_CriticalPortraits_maxVal_mem
-- name    : CriticalPortraits.maxVal_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:16.442479+00:00
-- url     : https://prove2.me/theorems/1efbf276-5b23-450c-9f7f-99e999a81233
-- title:
--   Critical Portraits: max Val mem
-- statement:
--   The Critical Portraits construction uses the max Val mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L556-L557
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L556-L557

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

theorem CriticalPortraits.maxVal_mem {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) : maxVal S h ∈ S := by sorry
