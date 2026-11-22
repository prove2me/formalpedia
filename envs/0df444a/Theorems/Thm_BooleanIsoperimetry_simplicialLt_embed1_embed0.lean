-- Prove2me | Theorems.Thm_BooleanIsoperimetry_simplicialLt_embed1_embed0
-- name    : BooleanIsoperimetry.simplicialLt_embed1_embed0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:51.553237+00:00
-- url     : https://prove2.me/theorems/b0ecc20f-d375-4905-aadb-2949be0763c9
-- title:
--   Boolean Isoperimetry: simplicial Lt embed1 embed0
-- statement:
--   Comparing an `embed1` vertex with an `embed0` vertex reduces to cardinalities.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L506-L511
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L506-L511

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

theorem BooleanIsoperimetry.simplicialLt_embed1_embed0 {n : ℕ} (u w : Cube n) :
    simplicialLt (embed1 u) (embed0 w) ↔ u.card + 1 ≤ w.card := by sorry
