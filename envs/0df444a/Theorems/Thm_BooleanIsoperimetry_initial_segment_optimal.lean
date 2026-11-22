-- Prove2me | Theorems.Thm_BooleanIsoperimetry_initial_segment_optimal
-- name    : BooleanIsoperimetry.initial_segment_optimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:54.115068+00:00
-- url     : https://prove2.me/theorems/599728b2-a847-41b1-baae-dc4534434a90
-- title:
--   Boolean Isoperimetry: initial segment optimal
-- statement:
--   The Boolean Isoperimetry construction uses the initial segment optimal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2126-L2133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2126-L2133

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

theorem BooleanIsoperimetry.initial_segment_optimal {n : ℕ} (k0 k1 : ℕ) (hk0 : k0 ≤ 2 ^ n) (hk1 : k1 ≤ 2 ^ n) :
    (neighborhood 1 (simplicialInitSeg (n + 1) (k0 + k1))).card ≤
    (neighborhood 1 (simplicialInitSeg n k0) ∪ simplicialInitSeg n k1).card +
    (neighborhood 1 (simplicialInitSeg n k1) ∪ simplicialInitSeg n k0).card := by sorry
