-- Prove2me | Theorems.Thm_BooleanIsoperimetry_binomPrefix_card_le_rank
-- name    : BooleanIsoperimetry.binomPrefix_card_le_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:00.684854+00:00
-- url     : https://prove2.me/theorems/3a560657-5cec-480c-add8-a656be63f591
-- title:
--   Boolean Isoperimetry: binom Prefix card le rank
-- statement:
--   Layer lower bound on `rank`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L330-L334
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L330-L334

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

theorem BooleanIsoperimetry.binomPrefix_card_le_rank {n : ℕ} (w : Cube n) :
    binomPrefix n w.card ≤ rank w := by sorry
