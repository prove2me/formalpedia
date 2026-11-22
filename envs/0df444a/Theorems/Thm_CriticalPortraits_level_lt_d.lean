-- Prove2me | Theorems.Thm_CriticalPortraits_level_lt_d
-- name    : CriticalPortraits.level_lt_d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:40.251299+00:00
-- url     : https://prove2.me/theorems/33c1cae2-87ac-4bdc-9e7d-6436883a180f
-- title:
--   Critical Portraits: level lt d
-- statement:
--   Every position has level `< d`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L197-L203
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L197-L203

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators

theorem CriticalPortraits.level_lt_d {d m : ℕ} (_hm : 0 < m) (x : ZMod (d * m)) [NeZero (d * m)] : x.val / m < d := by sorry
