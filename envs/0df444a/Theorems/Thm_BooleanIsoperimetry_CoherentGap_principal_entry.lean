-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_principal_entry
-- name    : BooleanIsoperimetry.CoherentGap.principal_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:13.870811+00:00
-- url     : https://prove2.me/theorems/bee7433f-20e3-4a77-b743-eae819f97e53
-- title:
--   Coherent Gap: principal entry
-- statement:
--   The Coherent Gap construction uses the principal entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L251-L272
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L251-L272

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

theorem BooleanIsoperimetry.CoherentGap.principal_entry (offset : ℕ) (coordinate : Fin (offset + 2)) :
    principal offset coordinate = -1 ∨
      principal offset coordinate = 0 ∨
      principal offset coordinate = 1 := by sorry
