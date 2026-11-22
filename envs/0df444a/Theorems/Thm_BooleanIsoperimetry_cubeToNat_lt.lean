-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cubeToNat_lt
-- name    : BooleanIsoperimetry.cubeToNat_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:46.084638+00:00
-- url     : https://prove2.me/theorems/516e7ede-5692-42cb-8b89-5afec247cbe7
-- title:
--   Boolean Isoperimetry: cube To Nat lt
-- statement:
--   `cubeToNat` of any vertex of the `n`-cube is `< 2^n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L342-L343
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L342-L343

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

theorem BooleanIsoperimetry.cubeToNat_lt {n : ℕ} (u : Cube n) : cubeToNat u < 2 ^ n := by sorry
