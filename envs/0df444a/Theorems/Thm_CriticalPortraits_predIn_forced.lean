-- Prove2me | Theorems.Thm_CriticalPortraits_predIn_forced
-- name    : CriticalPortraits.predIn_forced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:05.964967+00:00
-- url     : https://prove2.me/theorems/87c604a0-5d58-4b35-a0a8-998123f2964c
-- title:
--   Critical Portraits: pred In forced
-- statement:
--   The Critical Portraits construction uses the pred In forced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L769-L825
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L769-L825

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

theorem CriticalPortraits.predIn_forced [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P₁ P₂ : Finset (Finset (ZMod (d * m)))} (h₁ : Portrait d m P₁) (h₂ : Portrait d m P₂)
    (hT : T P₁ = T P₂) {x : ZMod (d * m)} (hx₁ : x ∈ T P₁) (hx₂ : x ∈ T P₂) :
    predIn P₁ x hx₁ = predIn P₂ x hx₂ := by sorry
