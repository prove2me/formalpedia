-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_principal_dot
-- name    : BooleanIsoperimetry.CoherentGap.principal_dot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:26.943729+00:00
-- url     : https://prove2.me/theorems/0bb4269e-2942-4a5e-9130-00dd8954d1ef
-- title:
--   Coherent Gap: principal dot
-- statement:
--   The Coherent Gap construction uses the principal dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L507-L544
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L507-L544

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

theorem BooleanIsoperimetry.CoherentGap.principal_dot (offset : ℕ)
    (hblock :
      conwayGuyHeight (offset + 2) -
          ∑ index : Fin (guide (offset + 2)),
            conwayGuyHeight (offset + 2 - index.val - 1) +
        ∑ index : Fin (guide (offset + 2) - 1),
          conwayGuyHeight (triangular index.val) = 1) :
    dot (principal offset) (conwayGuyArithmetic.weights (offset + 2)) = 1 := by sorry
