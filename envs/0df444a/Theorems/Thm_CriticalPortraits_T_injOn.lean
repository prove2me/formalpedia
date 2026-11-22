-- Prove2me | Theorems.Thm_CriticalPortraits_T_injOn
-- name    : CriticalPortraits.T_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:05.47595+00:00
-- url     : https://prove2.me/theorems/29a39e2a-dc89-4c05-a1a9-9d3f36dae27d
-- title:
--   Critical Portraits: T inj On
-- statement:
--   **INJECTIVITY (`Set.InjOn` form, the stated target).**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L1087-L1089
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L1087-L1089

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

theorem CriticalPortraits.T_injOn (hd : 0 < d) (hm : 0 < m) :
    Set.InjOn (T (N := d*m)) {P | Portrait d m P} := by sorry
