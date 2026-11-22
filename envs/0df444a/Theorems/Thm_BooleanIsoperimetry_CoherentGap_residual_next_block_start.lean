-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_residual_next_block_start
-- name    : BooleanIsoperimetry.CoherentGap.residual_next_block_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:37.336831+00:00
-- url     : https://prove2.me/theorems/5b79cd1e-bb66-4f1a-8190-3dcd86135277
-- title:
--   Coherent Gap: residual next block start
-- statement:
--   The Coherent Gap construction uses the residual next block start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L214-L257
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L214-L257

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

theorem BooleanIsoperimetry.CoherentGap.residual_next_block_start (previous : ℕ) :
    residual (previous + 2) (triangular (previous + 1) + 2) =
      residual (previous + 1) (triangular (previous + 1) + 1) -
        conwayGuyHeight (triangular previous) := by sorry
