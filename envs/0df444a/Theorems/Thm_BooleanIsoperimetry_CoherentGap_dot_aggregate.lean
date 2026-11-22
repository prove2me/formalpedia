-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_dot_aggregate
-- name    : BooleanIsoperimetry.CoherentGap.dot_aggregate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:31.486071+00:00
-- url     : https://prove2.me/theorems/13a2bf90-e003-4319-a5a4-8259bd87691b
-- title:
--   Coherent Gap: dot aggregate
-- statement:
--   The Coherent Gap construction uses the dot aggregate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/CoherentGap.lean#L83-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/CoherentGap.lean#L83-L93

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap

theorem BooleanIsoperimetry.CoherentGap.dot_aggregate {n : ℕ} (relations : List (Relation n)) (weights : Relation n) :
    dot (aggregate relations) weights =
      (relations.map fun relation => dot relation weights).sum := by sorry
