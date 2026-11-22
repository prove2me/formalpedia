-- Prove2me | Theorems.Thm_BooleanIsoperimetry_rank_lt_binomPrefix_iff
-- name    : BooleanIsoperimetry.rank_lt_binomPrefix_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:46.891873+00:00
-- url     : https://prove2.me/theorems/2d9c54d8-07c4-433e-b066-2604c54644a8
-- title:
--   Boolean Isoperimetry: rank lt binom Prefix iff
-- statement:
--   `rank` versus cardinality: `rank w < binomPrefix n c ↔ w.card < c`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L321-L327
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L321-L327

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

theorem BooleanIsoperimetry.rank_lt_binomPrefix_iff {n c : ℕ} (w : Cube n) :
    rank w < binomPrefix n c ↔ w.card < c := by sorry
