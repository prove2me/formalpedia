-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_coordinateSum_sub
-- name    : BooleanIsoperimetry.CoherentGap.coordinateSum_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:01.248097+00:00
-- url     : https://prove2.me/theorems/25f65ed8-e4c2-42de-b628-d855aebba90e
-- title:
--   Coherent Gap: coordinate Sum sub
-- statement:
--   The Coherent Gap construction uses the coordinate Sum sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L163-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L163-L166

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

theorem BooleanIsoperimetry.CoherentGap.coordinateSum_sub {n : ℕ} (first second : Relation n) :
    coordinateSum (first - second) =
      coordinateSum first - coordinateSum second := by sorry
