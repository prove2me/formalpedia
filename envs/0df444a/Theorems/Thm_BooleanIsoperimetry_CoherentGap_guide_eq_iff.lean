-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_guide_eq_iff
-- name    : BooleanIsoperimetry.CoherentGap.guide_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:22.895798+00:00
-- url     : https://prove2.me/theorems/c5486fd6-9400-4b2f-9f38-a99b1d6948bb
-- title:
--   Coherent Gap: guide eq iff
-- statement:
--   The Coherent Gap construction uses the guide eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L47-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L47-L66

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

theorem BooleanIsoperimetry.CoherentGap.guide_eq_iff {dimension width : ℕ} (hwidth : 0 < width) :
    guide dimension = width ↔
      triangular (width - 1) + 2 ≤ dimension ∧
        dimension ≤ triangular width + 1 := by sorry
