-- Prove2me | Theorems.Thm_BooleanIsoperimetry_union_initSeg_card_le
-- name    : BooleanIsoperimetry.union_initSeg_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:55.189308+00:00
-- url     : https://prove2.me/theorems/8ee819e7-ec60-45ea-8313-eb8e6f7c8d58
-- title:
--   Boolean Isoperimetry: union init Seg card le
-- statement:
--   The Boolean Isoperimetry construction uses the union init Seg card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2149-L2161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2149-L2161

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

theorem BooleanIsoperimetry.union_initSeg_card_le {n a b : ℕ} {B C : Finset (Cube n)}
    (hHa : (neighborhood 1 (simplicialInitSeg n a)).card ≤ (neighborhood 1 B).card)
    (hb : C.card = b) (hb2 : b ≤ 2 ^ n) :
    (neighborhood 1 (simplicialInitSeg n a) ∪ simplicialInitSeg n b).card ≤
      (neighborhood 1 B ∪ C).card := by sorry
