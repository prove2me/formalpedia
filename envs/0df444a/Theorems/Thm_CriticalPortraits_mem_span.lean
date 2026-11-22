-- Prove2me | Theorems.Thm_CriticalPortraits_mem_span
-- name    : CriticalPortraits.mem_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:11.875235+00:00
-- url     : https://prove2.me/theorems/222cf3a5-e75b-48b2-bb76-3f6cf8c444dc
-- title:
--   Critical Portraits: mem span
-- statement:
--   **Lemma 2 (hull edge).** Every block element's `.val` lies within the span.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L584-L586
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L584-L586

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

theorem CriticalPortraits.mem_span {N : ℕ} {S : Finset (ZMod N)} (h : S.Nonempty) {x : ZMod N} (hx : x ∈ S) :
    spanLo S h ≤ x.val ∧ x.val ≤ spanHi S h := by sorry
