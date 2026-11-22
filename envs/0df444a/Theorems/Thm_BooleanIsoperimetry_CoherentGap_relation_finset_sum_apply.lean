-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_relation_finset_sum_apply
-- name    : BooleanIsoperimetry.CoherentGap.relation_finset_sum_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:10.429822+00:00
-- url     : https://prove2.me/theorems/3e0b4738-2e9f-4d21-a263-8f3fd960cff2
-- title:
--   Coherent Gap: relation finset sum apply
-- statement:
--   The Coherent Gap construction uses the relation finset sum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L224-L232
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L224-L232

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

theorem BooleanIsoperimetry.CoherentGap.relation_finset_sum_apply {n : ℕ} {α : Type}
    (set : Finset α) (relations : α → Relation n) (coordinate : Fin n) :
    (∑ index ∈ set, relations index) coordinate =
      ∑ index ∈ set, relations index coordinate := by sorry
