-- Prove2me | Theorems.Thm_AbstractLaminar_topEdges_card_le
-- name    : AbstractLaminar.topEdges_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:18.332612+00:00
-- url     : https://prove2.me/theorems/df5a2cf8-4e66-44de-a575-ec6387a97d08
-- title:
--   Abstract Laminar: top Edges card le
-- statement:
--   At most one top edge (intervals identify edges).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L298-L303
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L298-L303

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
set_option autoImplicit true
@[expose] public section
public section
open AbstractLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
variable {a b : ℕ}

theorem AbstractLaminar.topEdges_card_le : (topEdges fam a b).card ≤ 1 := by sorry
