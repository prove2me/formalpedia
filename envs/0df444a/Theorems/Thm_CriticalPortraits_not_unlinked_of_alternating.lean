-- Prove2me | Theorems.Thm_CriticalPortraits_not_unlinked_of_alternating
-- name    : CriticalPortraits.not_unlinked_of_alternating
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:36.743145+00:00
-- url     : https://prove2.me/theorems/57256210-6398-421a-b3b4-771fb11a4137
-- title:
--   Critical Portraits: not unlinked of alternating
-- statement:
--   The crossing witness Lemma A / Seam / Bridge will call: a strictly-alternating quadruple
--       `a1 < b1 < a2 < b2` (linear `.val` order) with `a1,a2 ∈ A`, `b1,b2 ∈ B` contradicts
--       `Unlinked A B`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L95-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L95-L98

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

theorem CriticalPortraits.not_unlinked_of_alternating {N : ℕ} {A B : Finset (ZMod N)}
    {a1 a2 b1 b2 : ZMod N} (ha1 : a1 ∈ A) (ha2 : a2 ∈ A) (hb1 : b1 ∈ B) (hb2 : b2 ∈ B)
    (h1 : a1.val < b1.val) (h2 : b1.val < a2.val) (h3 : a2.val < b2.val) :
    ¬ Unlinked A B := by sorry
