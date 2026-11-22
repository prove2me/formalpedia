-- Prove2me | Theorems.Thm_BooleanIsoperimetry_choose_succ_dim
-- name    : BooleanIsoperimetry.choose_succ_dim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:07.370801+00:00
-- url     : https://prove2.me/theorems/d0827b78-7e71-4cc6-abbc-0f2521e6ba1c
-- title:
--   Boolean Isoperimetry: choose succ dim
-- statement:
--   `Nat.choose (n+1) r` splits as `Nat.choose n r + choosePred n r`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L154-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L154-L158

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

theorem BooleanIsoperimetry.choose_succ_dim (n r : ℕ) :
    Nat.choose (n + 1) r = Nat.choose n r + choosePred n r := by sorry
