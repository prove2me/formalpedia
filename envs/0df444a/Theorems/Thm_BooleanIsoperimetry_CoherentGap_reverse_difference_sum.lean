-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_reverse_difference_sum
-- name    : BooleanIsoperimetry.CoherentGap.reverse_difference_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:32.773425+00:00
-- url     : https://prove2.me/theorems/8c0e85f1-44b2-4270-b2d7-85a988ef5737
-- title:
--   Coherent Gap: reverse difference sum
-- statement:
--   The Coherent Gap construction uses the reverse difference sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L118-L150
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L118-L150

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyHeight
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap

theorem BooleanIsoperimetry.CoherentGap.reverse_difference_sum (dimension : ℕ) :
    ∀ width : ℕ, width ≤ dimension →
      (∑ index : Fin width,
          (conwayGuyDifference (dimension - index.val - 1) : ℤ)) =
        conwayGuyHeight dimension -
          conwayGuyHeight (dimension - width)
  := by sorry
