-- Prove2me | Theorems.Thm_BooleanIsoperimetry_simplicialLt_embed1_embed1
-- name    : BooleanIsoperimetry.simplicialLt_embed1_embed1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:45.815597+00:00
-- url     : https://prove2.me/theorems/ae76e104-82e2-4e4b-bee5-28238e0b1b71
-- title:
--   Boolean Isoperimetry: simplicial Lt embed1 embed1
-- statement:
--   `embed1` reflects (and preserves) the strict simplicial order.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L346-L350
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L346-L350

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

theorem BooleanIsoperimetry.simplicialLt_embed1_embed1 {n : ℕ} (u w : Cube n) :
    simplicialLt (embed1 u) (embed1 w) ↔ simplicialLt u w := by sorry
