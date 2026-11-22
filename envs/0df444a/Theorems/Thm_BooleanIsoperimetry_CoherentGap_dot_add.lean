-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_dot_add
-- name    : BooleanIsoperimetry.CoherentGap.dot_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:47.518813+00:00
-- url     : https://prove2.me/theorems/b2882d2b-fa8c-47ec-8a8d-66205fa64d24
-- title:
--   Coherent Gap: dot add
-- statement:
--   The Coherent Gap construction uses the dot add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/CoherentGap.lean#L79-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/CoherentGap.lean#L79-L81

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

theorem BooleanIsoperimetry.CoherentGap.dot_add {n : ℕ} (first second weights : Relation n) :
    dot (first + second) weights = dot first weights + dot second weights := by sorry
