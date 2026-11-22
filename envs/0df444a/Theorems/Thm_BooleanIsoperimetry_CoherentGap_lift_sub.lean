-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_lift_sub
-- name    : BooleanIsoperimetry.CoherentGap.lift_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:17.897331+00:00
-- url     : https://prove2.me/theorems/9eeb7a69-4252-47db-995b-1a6838cc2991
-- title:
--   Coherent Gap: lift sub
-- statement:
--   The Coherent Gap construction uses the lift sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L274-L280
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L274-L280

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

theorem BooleanIsoperimetry.CoherentGap.lift_sub {n : ℕ} (first second : Relation n) :
    lift (first - second) = lift first - lift second := by sorry
