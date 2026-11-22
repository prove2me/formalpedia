-- Prove2me | Theorems.Thm_CriticalPortraits_edgeStep_forced
-- name    : CriticalPortraits.edgeStep_forced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:59.319168+00:00
-- url     : https://prove2.me/theorems/4b36383e-5e2c-4c2a-802e-56263a121c50
-- title:
--   Critical Portraits: edge Step forced
-- statement:
--   With forced predecessors and equal survivor sets, the `edgeStep` relations agree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L959-L968
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L959-L968

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

theorem CriticalPortraits.edgeStep_forced [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P₁ P₂ : Finset (Finset (ZMod (d * m)))} (h₁ : Portrait d m P₁) (h₂ : Portrait d m P₂)
    (hT : T P₁ = T P₂) {u v : ZMod (d * m)} (hstep : edgeStep P₁ u v) : edgeStep P₂ u v := by sorry
