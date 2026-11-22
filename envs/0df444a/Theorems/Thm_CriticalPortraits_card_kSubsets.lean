-- Prove2me | Theorems.Thm_CriticalPortraits_card_kSubsets
-- name    : CriticalPortraits.card_kSubsets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:36.098326+00:00
-- url     : https://prove2.me/theorems/3f1f1f8a-4a60-4a30-bece-ed850056b935
-- title:
--   Critical Portraits: card k Subsets
-- statement:
--   The `k`-subsets of `Z_N` number `C(N, k)` (the count numerator).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Core.lean#L34-L36
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Core.lean#L34-L36

module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Core
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset

theorem CriticalPortraits.card_kSubsets (N k : ℕ) [NeZero N] :
    Fintype.card {S : Finset (ZMod N) // S.card = k} = N.choose k := by sorry
