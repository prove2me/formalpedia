-- Prove2me | Theorems.Thm_BooleanIsoperimetry_empty_mem_initSeg
-- name    : BooleanIsoperimetry.empty_mem_initSeg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:52.373732+00:00
-- url     : https://prove2.me/theorems/5fa81f13-de0b-44e2-a63b-2a8ee1ecc977
-- title:
--   Boolean Isoperimetry: empty mem init Seg
-- statement:
--   The empty vertex lies in every nonempty initial segment.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L514-L521
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L514-L521

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

theorem BooleanIsoperimetry.empty_mem_initSeg {n k : ℕ} (hk : 1 ≤ k) :
    (∅ : Cube n) ∈ simplicialInitSeg n k := by sorry
