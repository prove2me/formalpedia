-- Prove2me | Theorems.Thm_BooleanIsoperimetry_gShift_embed0
-- name    : BooleanIsoperimetry.gShift_embed0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:56.076002+00:00
-- url     : https://prove2.me/theorems/40c2ccb3-56a6-4286-86ec-057bb0c1ebf1
-- title:
--   Boolean Isoperimetry: g Shift embed0
-- statement:
--   `gShift` on the 0-slice commutes with the embedding.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L557-L591
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L557-L591

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

theorem BooleanIsoperimetry.gShift_embed0 {n : ℕ} (v : Cube n) :
    gShift (embed0 v) = embed0 (gShift v) := by sorry
