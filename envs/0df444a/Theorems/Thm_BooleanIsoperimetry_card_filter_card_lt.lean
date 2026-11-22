-- Prove2me | Theorems.Thm_BooleanIsoperimetry_card_filter_card_lt
-- name    : BooleanIsoperimetry.card_filter_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:44.789021+00:00
-- url     : https://prove2.me/theorems/5f552828-875b-4f1e-a8a8-ddd0c0c6ed3f
-- title:
--   Boolean Isoperimetry: card filter card lt
-- statement:
--   The number of vertices of the `n`-cube with cardinality `< c` is `binomPrefix n c`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L289-L303
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L289-L303

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.card_filter_card_lt (n c : ℕ) :
    (Finset.univ.filter (fun w : Cube n => w.card < c)).card = binomPrefix n c := by sorry
