-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_guide_at_triangular_end
-- name    : BooleanIsoperimetry.CoherentGap.guide_at_triangular_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:27.184803+00:00
-- url     : https://prove2.me/theorems/8e86cd1a-5223-4eb2-b9d0-c3ede2a98f18
-- title:
--   Coherent Gap: guide at triangular end
-- statement:
--   The Coherent Gap construction uses the guide at triangular end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L37-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L37-L45

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

theorem BooleanIsoperimetry.CoherentGap.guide_at_triangular_end (width : ℕ) :
    guide (triangular width + 1) = width := by sorry
