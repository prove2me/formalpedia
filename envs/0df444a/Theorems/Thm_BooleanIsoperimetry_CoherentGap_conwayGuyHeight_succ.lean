-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_conwayGuyHeight_succ
-- name    : BooleanIsoperimetry.CoherentGap.conwayGuyHeight_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:22.802565+00:00
-- url     : https://prove2.me/theorems/60aae318-9709-43a5-b6af-452f6452f152
-- title:
--   Coherent Gap: conway Guy Height succ
-- statement:
--   The Coherent Gap construction uses the conway Guy Height succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L436-L439
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L436-L439

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap

theorem BooleanIsoperimetry.CoherentGap.conwayGuyHeight_succ (dimension : ℕ) :
    conwayGuyHeight (dimension + 1) =
      conwayGuyHeight dimension + conwayGuyDifference dimension := by sorry
