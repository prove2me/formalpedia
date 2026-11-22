-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_positiveIndex_injective
-- name    : BooleanIsoperimetry.CoherentGap.positiveIndex_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:10.031058+00:00
-- url     : https://prove2.me/theorems/646f8eed-6f3e-470d-92db-563620296ef8
-- title:
--   Coherent Gap: positive Index injective
-- statement:
--   The Coherent Gap construction uses the positive Index injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L192-L196
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L192-L196

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

theorem BooleanIsoperimetry.CoherentGap.positiveIndex_injective (offset : ℕ) :
    Function.Injective (positiveIndex offset) := by sorry
