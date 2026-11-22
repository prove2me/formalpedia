-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_aggregate
-- name    : BooleanIsoperimetry.CoherentGap.realDot_aggregate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:34.387796+00:00
-- url     : https://prove2.me/theorems/c5fc7afd-7b35-4bb7-979c-5190842e2cfe
-- title:
--   Coherent Gap: real Dot aggregate
-- statement:
--   The Coherent Gap construction uses the real Dot aggregate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/CoherentGap.lean#L465-L476
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/CoherentGap.lean#L465-L476

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

theorem BooleanIsoperimetry.CoherentGap.realDot_aggregate {n : ℕ} (relations : List (Relation n))
    (candidate : Fin n → ℝ) :
    realDot (aggregate relations) candidate =
      (relations.map fun relation => realDot relation candidate).sum := by sorry
