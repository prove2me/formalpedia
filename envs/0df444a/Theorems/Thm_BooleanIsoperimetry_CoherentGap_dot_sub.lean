-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_dot_sub
-- name    : BooleanIsoperimetry.CoherentGap.dot_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:21.165961+00:00
-- url     : https://prove2.me/theorems/7e554556-9216-4741-9e36-72c7057a71b8
-- title:
--   Coherent Gap: dot sub
-- statement:
--   The Coherent Gap construction uses the dot sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L492-L495
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L492-L495

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

theorem BooleanIsoperimetry.CoherentGap.dot_sub {n : ℕ} (first second weights : Relation n) :
    dot (first - second) weights =
      dot first weights - dot second weights := by sorry
