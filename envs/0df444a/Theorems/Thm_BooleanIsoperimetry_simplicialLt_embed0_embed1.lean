-- Prove2me | Theorems.Thm_BooleanIsoperimetry_simplicialLt_embed0_embed1
-- name    : BooleanIsoperimetry.simplicialLt_embed0_embed1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:48.438877+00:00
-- url     : https://prove2.me/theorems/806440c2-0b93-4c8c-9524-71bbe48cdb5d
-- title:
--   Boolean Isoperimetry: simplicial Lt embed0 embed1
-- statement:
--   Comparing an `embed0` vertex with an `embed1` vertex reduces to cardinalities.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L353-L358
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L353-L358

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

theorem BooleanIsoperimetry.simplicialLt_embed0_embed1 {n : ℕ} (u w : Cube n) :
    simplicialLt (embed0 u) (embed1 w) ↔ u.card < w.card + 1 := by sorry
