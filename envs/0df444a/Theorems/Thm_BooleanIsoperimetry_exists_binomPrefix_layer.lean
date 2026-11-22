-- Prove2me | Theorems.Thm_BooleanIsoperimetry_exists_binomPrefix_layer
-- name    : BooleanIsoperimetry.exists_binomPrefix_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:39:54.446813+00:00
-- url     : https://prove2.me/theorems/4ff7ef03-209e-4b4f-b4f7-7a7686b384ed
-- title:
--   Boolean Isoperimetry: exists binom Prefix layer
-- statement:
--   The Boolean Isoperimetry construction uses the exists binom Prefix layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L579-L597
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L579-L597

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

theorem BooleanIsoperimetry.exists_binomPrefix_layer (N b : ℕ) (hb : b < 2 ^ N) :
    ∃ r, r ≤ N ∧ binomPrefix N r ≤ b ∧ b < binomPrefix N (r + 1) := by sorry
