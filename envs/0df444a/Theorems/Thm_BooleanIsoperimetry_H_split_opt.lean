-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_split_opt
-- name    : BooleanIsoperimetry.H_split_opt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:53.680162+00:00
-- url     : https://prove2.me/theorems/6d0952f8-f0de-4e57-add8-df85d57a629b
-- title:
--   Boolean Isoperimetry: H split opt
-- statement:
--   The Boolean Isoperimetry construction uses the H split opt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2101-L2114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2101-L2114

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

theorem BooleanIsoperimetry.H_split_opt {n a b : ℕ} (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) :
    max (H n (slice0 (simplicialInitSeg (n + 1) (a + b))).card)
        (slice1 (simplicialInitSeg (n + 1) (a + b))).card +
    max (H n (slice1 (simplicialInitSeg (n + 1) (a + b))).card)
        (slice0 (simplicialInitSeg (n + 1) (a + b))).card
    ≤ max (H n a) b + max (H n b) a := by sorry
