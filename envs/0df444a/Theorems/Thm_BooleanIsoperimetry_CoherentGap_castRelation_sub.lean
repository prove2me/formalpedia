-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_castRelation_sub
-- name    : BooleanIsoperimetry.CoherentGap.castRelation_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:17.802803+00:00
-- url     : https://prove2.me/theorems/bf846a54-423c-4aa0-9fcc-6585d5cffffe
-- title:
--   Coherent Gap: cast Relation sub
-- statement:
--   The Coherent Gap construction uses the cast Relation sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L335-L341
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L335-L341

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

theorem BooleanIsoperimetry.CoherentGap.castRelation_sub {firstDimension secondDimension : ℕ}
    (hdimension : firstDimension = secondDimension)
    (first second : Relation firstDimension) :
    castRelation hdimension (first - second) =
      castRelation hdimension first - castRelation hdimension second := by sorry
