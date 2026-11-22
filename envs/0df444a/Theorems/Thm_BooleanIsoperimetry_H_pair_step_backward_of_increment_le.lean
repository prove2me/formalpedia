-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_pair_step_backward_of_increment_le
-- name    : BooleanIsoperimetry.H_pair_step_backward_of_increment_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:40:02.722057+00:00
-- url     : https://prove2.me/theorems/7a351aec-74d8-4eea-b55d-207c9add58ab
-- title:
--   Boolean Isoperimetry: H pair step backward of increment le
-- statement:
--   The Boolean Isoperimetry construction uses the H pair step backward of increment le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L543-L557
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L543-L557

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.H_pair_step_backward_of_increment_le (N x y : ℕ)
    (hy : 1 ≤ y) (hinc : HIncrement N x ≤ HIncrement N (y - 1)) :
    H N (x + 1) + H N (y - 1) ≤ H N x + H N y := by sorry
