-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_residual_eq_block_start
-- name    : BooleanIsoperimetry.CoherentGap.residual_eq_block_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:22.346361+00:00
-- url     : https://prove2.me/theorems/6a174994-a11f-4565-ba3e-2790e253130c
-- title:
--   Coherent Gap: residual eq block start
-- statement:
--   The Coherent Gap construction uses the residual eq block start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L196-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L196-L212

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

theorem BooleanIsoperimetry.CoherentGap.residual_eq_block_start {width dimension : ℕ}
    (hwidth : 0 < width)
    (hguide : guide dimension = width) :
    residual width dimension =
      residual width (triangular (width - 1) + 2) := by sorry
