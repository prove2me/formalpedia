-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_residual_succ_width
-- name    : BooleanIsoperimetry.CoherentGap.residual_succ_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:32.710404+00:00
-- url     : https://prove2.me/theorems/9ed97f59-a572-4377-bbb0-b5a8154fe09a
-- title:
--   Coherent Gap: residual succ width
-- statement:
--   The Coherent Gap construction uses the residual succ width property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L175-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L175-L194

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

theorem BooleanIsoperimetry.CoherentGap.residual_succ_width (width dimension : ℕ) :
    residual (width + 1) (dimension + 1) =
      residual width dimension +
        conwayGuyDifference dimension -
          conwayGuyHeight dimension := by sorry
