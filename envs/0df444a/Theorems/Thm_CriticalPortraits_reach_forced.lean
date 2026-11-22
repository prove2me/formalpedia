-- Prove2me | Theorems.Thm_CriticalPortraits_reach_forced
-- name    : CriticalPortraits.reach_forced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:58.942614+00:00
-- url     : https://prove2.me/theorems/7c5ecf0c-30cd-4e54-8204-21e27b88b1bc
-- title:
--   Critical Portraits: reach forced
-- statement:
--   Reachability transfers between portraits with forced predecessors.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L971-L978
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L971-L978

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

theorem CriticalPortraits.reach_forced [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P₁ P₂ : Finset (Finset (ZMod (d * m)))} (h₁ : Portrait d m P₁) (h₂ : Portrait d m P₂)
    (hT : T P₁ = T P₂) {u v : ZMod (d * m)}
    (hreach : Relation.ReflTransGen (edgeStep P₁) u v) :
    Relation.ReflTransGen (edgeStep P₂) u v := by sorry
