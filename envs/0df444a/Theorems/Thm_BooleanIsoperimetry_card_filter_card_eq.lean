-- Prove2me | Theorems.Thm_BooleanIsoperimetry_card_filter_card_eq
-- name    : BooleanIsoperimetry.card_filter_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:43.952115+00:00
-- url     : https://prove2.me/theorems/795541eb-54c2-4933-8f90-6830174efc15
-- title:
--   Boolean Isoperimetry: card filter card eq
-- statement:
--   The number of vertices of the `n`-cube with cardinality exactly `c` is `C(n,c)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L281-L286
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L281-L286

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

theorem BooleanIsoperimetry.card_filter_card_eq (n c : ℕ) :
    (Finset.univ.filter (fun w : Cube n => w.card = c)).card = Nat.choose n c := by sorry
