-- Prove2me | Theorems.Thm_CriticalPortraits_sep_master
-- name    : CriticalPortraits.sep_master
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:33.736179+00:00
-- url     : https://prove2.me/theorems/0d3426e1-e8ac-4e66-a45d-3483cb6cd6ed
-- title:
--   Critical Portraits: sep master
-- statement:
--   **The master separation inequality (M).** One level of separation beats any column
--       offset: for columns `p, q < m` and levels `a < c`, `p + a*m < q + c*m`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L291-L295
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L291-L295

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

theorem CriticalPortraits.sep_master {m : ℕ} {p q a c : ℕ} (hp : p < m) (_hq : q < m) (hac : a < c) :
    p + a * m < q + c * m := by sorry
