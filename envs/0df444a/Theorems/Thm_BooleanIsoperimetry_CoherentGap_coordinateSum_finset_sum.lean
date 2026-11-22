-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_coordinateSum_finset_sum
-- name    : BooleanIsoperimetry.CoherentGap.coordinateSum_finset_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:11.896626+00:00
-- url     : https://prove2.me/theorems/38d5ed78-54ba-4aa4-aa1d-37d94ccb743a
-- title:
--   Coherent Gap: coordinate Sum finset sum
-- statement:
--   The Coherent Gap construction uses the coordinate Sum finset sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L168-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L168-L176

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

theorem BooleanIsoperimetry.CoherentGap.coordinateSum_finset_sum {n : ℕ} {α : Type}
    (set : Finset α) (relations : α → Relation n) :
    coordinateSum (∑ index ∈ set, relations index) =
      ∑ index ∈ set, coordinateSum (relations index) := by sorry
