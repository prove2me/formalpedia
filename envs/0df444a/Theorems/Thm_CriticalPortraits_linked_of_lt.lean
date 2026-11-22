-- Prove2me | Theorems.Thm_CriticalPortraits_linked_of_lt
-- name    : CriticalPortraits.linked_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:37.301566+00:00
-- url     : https://prove2.me/theorems/c7a2b19b-7e69-4a81-93ef-e8f519d6bb0b
-- title:
--   Critical Portraits: linked of lt
-- statement:
--   A crossing quadruple in strict val-order makes `A, B` linked (the (M)-witness hook).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L298-L302
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L298-L302

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

theorem CriticalPortraits.linked_of_lt {N : ℕ} {A B : Finset (ZMod N)} {a1 a2 b1 b2 : ZMod N}
    (ha1 : a1 ∈ A) (ha2 : a2 ∈ A) (hb1 : b1 ∈ B) (hb2 : b2 ∈ B)
    (h1 : a1.val < b1.val) (h2 : b1.val < a2.val) (h3 : a2.val < b2.val) :
    Linked A B := by sorry
