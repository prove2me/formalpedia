-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_succ_slice
-- name    : BooleanIsoperimetry.H_succ_slice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:34.414804+00:00
-- url     : https://prove2.me/theorems/ab20736c-4079-4e98-a8ca-556c5999e562
-- title:
--   Boolean Isoperimetry: H succ slice
-- statement:
--   The Boolean Isoperimetry construction uses the H succ slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L905-L957
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L905-L957

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

theorem BooleanIsoperimetry.H_succ_slice {n k : ℕ} :
    H (n + 1) k =
      max (H n (slice0 (simplicialInitSeg (n + 1) k)).card)
          (slice1 (simplicialInitSeg (n + 1) k)).card +
      max (H n (slice1 (simplicialInitSeg (n + 1) k)).card)
          (slice0 (simplicialInitSeg (n + 1) k)).card := by sorry
