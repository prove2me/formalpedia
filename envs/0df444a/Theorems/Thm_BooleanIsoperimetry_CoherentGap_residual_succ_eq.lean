-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_residual_succ_eq
-- name    : BooleanIsoperimetry.CoherentGap.residual_succ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:28.154936+00:00
-- url     : https://prove2.me/theorems/2e767c6a-eada-4df3-8c7f-b86bb6776f63
-- title:
--   Coherent Gap: residual succ eq
-- statement:
--   The Coherent Gap construction uses the residual succ eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L80-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L80-L116

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

theorem BooleanIsoperimetry.CoherentGap.residual_succ_eq {width dimension : ℕ}
    (hdimension : 0 < dimension)
    (hwidth : width ≤ dimension)
    (hguide : guide (dimension + 1) = width) :
    residual width (dimension + 1) = residual width dimension := by sorry
