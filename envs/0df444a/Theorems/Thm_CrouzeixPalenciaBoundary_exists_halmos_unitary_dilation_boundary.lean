-- Prove2me | Theorems.Thm_CrouzeixPalenciaBoundary_exists_halmos_unitary_dilation_boundary
-- name    : CrouzeixPalenciaBoundary.exists_halmos_unitary_dilation_boundary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:17:55.767902+00:00
-- url     : https://prove2.me/theorems/5ec239fa-70cb-4336-8331-5f5e3f39477e
-- title:
--   Crouzeix Palencia Boundary: exists halmos unitary dilation boundary
-- statement:
--   The Crouzeix Palencia Boundary construction uses the exists halmos unitary dilation boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L80-L85
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L80-L85

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem CrouzeixPalenciaBoundary.exists_halmos_unitary_dilation_boundary
    (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ∃ U : WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E),
      U ∈ unitary (WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)) ∧
        ∀ x : E, (U (WithLp.toLp 2 (x, 0))).fst = T x := by sorry
