-- Prove2me | Theorems.Thm_BooleanIsoperimetry_lowCard_eq_initSeg
-- name    : BooleanIsoperimetry.lowCard_eq_initSeg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:44.587675+00:00
-- url     : https://prove2.me/theorems/5907ab98-3dc1-401f-a7de-9579ceef7865
-- title:
--   Boolean Isoperimetry: low Card eq init Seg
-- statement:
--   The set of low-cardinality vertices is exactly an initial segment.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L306-L318
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L306-L318

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

theorem BooleanIsoperimetry.lowCard_eq_initSeg (n c : ℕ) :
    Finset.univ.filter (fun w : Cube n => w.card < c)
      = simplicialInitSeg n (binomPrefix n c) := by sorry
