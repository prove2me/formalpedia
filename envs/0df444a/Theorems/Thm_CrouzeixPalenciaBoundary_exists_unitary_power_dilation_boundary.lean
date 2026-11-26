-- Prove2me | Theorems.Thm_CrouzeixPalenciaBoundary_exists_unitary_power_dilation_boundary
-- name    : CrouzeixPalenciaBoundary.exists_unitary_power_dilation_boundary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:18:04.231554+00:00
-- url     : https://prove2.me/theorems/495edde6-15ef-457a-87f8-f052fabbdd03
-- title:
--   Crouzeix Palencia Boundary: exists unitary power dilation boundary
-- statement:
--   The Crouzeix Palencia Boundary construction uses the exists unitary power dilation boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L87-L95
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L87-L95

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem CrouzeixPalenciaBoundary.exists_unitary_power_dilation_boundary
    (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (V : E →L[ℂ] H) (U : H →L[ℂ] H),
      (∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
        U ∈ unitary (H →L[ℂ] H) ∧
          ∀ (n : ℕ) (x : E),
            ContinuousLinearMap.adjoint V ((U ^ n) (V x)) = (T ^ n) x := by sorry
