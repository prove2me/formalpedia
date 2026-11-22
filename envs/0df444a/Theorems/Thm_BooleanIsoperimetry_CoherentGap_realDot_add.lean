-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_add
-- name    : BooleanIsoperimetry.CoherentGap.realDot_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:35.993816+00:00
-- url     : https://prove2.me/theorems/cf521b7b-3a07-4da9-b61f-7dabb0ad2a8f
-- title:
--   Coherent Gap: real Dot add
-- statement:
--   The Coherent Gap construction uses the real Dot add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/CoherentGap.lean#L459-L463
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/CoherentGap.lean#L459-L463

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

theorem BooleanIsoperimetry.CoherentGap.realDot_add {n : ℕ} (first second : Relation n)
    (candidate : Fin n → ℝ) :
    realDot (first + second) candidate =
      realDot first candidate + realDot second candidate := by sorry
