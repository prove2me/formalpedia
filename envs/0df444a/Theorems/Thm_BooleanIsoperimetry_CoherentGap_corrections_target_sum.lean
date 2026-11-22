-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_corrections_target_sum
-- name    : BooleanIsoperimetry.CoherentGap.corrections_target_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:21.5018+00:00
-- url     : https://prove2.me/theorems/99f449c5-c111-4c54-8a2e-1f10cca6459f
-- title:
--   Coherent Gap: corrections target sum
-- statement:
--   The Coherent Gap construction uses the corrections target sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L373-L381
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L373-L381

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

theorem BooleanIsoperimetry.CoherentGap.corrections_target_sum (offset : ℕ) :
    ((corrections offset).map Correction.target).sum =
      ∑ index : Fin (guide (offset + 2) - 1),
        (basis (negativeIndex offset index) -
          basis (⟨index.val + 1, by
            have hdeep := correction_deep_bound (dimension := offset + 2)
              (index := index.val) (by omega) index.isLt
            omega⟩ : Fin (offset + 2))) := by sorry
