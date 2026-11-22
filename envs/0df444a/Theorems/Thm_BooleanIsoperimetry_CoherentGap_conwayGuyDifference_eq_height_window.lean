-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_conwayGuyDifference_eq_height_window
-- name    : BooleanIsoperimetry.CoherentGap.conwayGuyDifference_eq_height_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:33.408008+00:00
-- url     : https://prove2.me/theorems/95ff49a8-f311-430b-b05f-d56e8440e779
-- title:
--   Coherent Gap: conway Guy Difference eq height window
-- statement:
--   The Coherent Gap construction uses the conway Guy Difference eq height window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L152-L173
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L152-L173

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

theorem BooleanIsoperimetry.CoherentGap.conwayGuyDifference_eq_height_window (dimension : ℕ)
    (hdimension : 0 < dimension) :
    (conwayGuyDifference dimension : ℤ) =
      conwayGuyHeight dimension -
        conwayGuyHeight (dimension - guide (dimension + 1)) := by sorry
