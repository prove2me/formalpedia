-- Prove2me | Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_initSeg_iff
-- name    : BooleanIsoperimetry.mem_neighborhood_initSeg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:16.058951+00:00
-- url     : https://prove2.me/theorems/8043f455-0b7a-4d1d-832d-9d385e0a27ac
-- title:
--   Boolean Isoperimetry: mem neighborhood init Seg iff
-- statement:
--   The Boolean Isoperimetry construction uses the mem neighborhood init Seg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L622-L628
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L622-L628

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.mem_neighborhood_initSeg_iff {n k : ℕ} {v : Cube n} :
    v ∈ neighborhood 1 (simplicialInitSeg n k) ↔ rank (gShift v) < k := by sorry
