-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_dot_finset_sum
-- name    : BooleanIsoperimetry.CoherentGap.dot_finset_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:20.932136+00:00
-- url     : https://prove2.me/theorems/8d57d9bd-47ae-42c3-9c02-4012aa0a8ba4
-- title:
--   Coherent Gap: dot finset sum
-- statement:
--   The Coherent Gap construction uses the dot finset sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L497-L505
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L497-L505

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

theorem BooleanIsoperimetry.CoherentGap.dot_finset_sum {n : ℕ} {α : Type}
    (set : Finset α) (relations : α → Relation n) (weights : Relation n) :
    dot (∑ index ∈ set, relations index) weights =
      ∑ index ∈ set, dot (relations index) weights := by sorry
