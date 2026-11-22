-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_correction_sum_succ
-- name    : BooleanIsoperimetry.CoherentGap.correction_sum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:39.437101+00:00
-- url     : https://prove2.me/theorems/07f285af-c9cf-4422-b376-02afdc4e47d7
-- title:
--   Coherent Gap: correction sum succ
-- statement:
--   The Coherent Gap construction uses the correction sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L259-L269
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L259-L269

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

theorem BooleanIsoperimetry.CoherentGap.correction_sum_succ (previous : ℕ) :
    (∑ index : Fin (previous + 1),
        conwayGuyHeight (triangular index.val)) =
      (∑ index : Fin previous,
          conwayGuyHeight (triangular index.val)) +
        conwayGuyHeight (triangular previous) := by sorry
