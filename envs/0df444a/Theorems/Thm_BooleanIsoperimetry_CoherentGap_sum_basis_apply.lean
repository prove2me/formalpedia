-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_sum_basis_apply
-- name    : BooleanIsoperimetry.CoherentGap.sum_basis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:16.051357+00:00
-- url     : https://prove2.me/theorems/aa3aafbb-eeae-404c-88bb-46b40ea0f871
-- title:
--   Coherent Gap: sum basis apply
-- statement:
--   The Coherent Gap construction uses the sum basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L234-L249
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L234-L249

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

theorem BooleanIsoperimetry.CoherentGap.sum_basis_apply {sourceDimension targetDimension : ℕ}
    (embedding : Fin sourceDimension → Fin targetDimension)
    (hinjective : Function.Injective embedding)
    (coordinate : Fin targetDimension) :
    (∑ index, basis (embedding index)) coordinate =
      if coordinate ∈ Finset.univ.image embedding then 1 else 0 := by sorry
