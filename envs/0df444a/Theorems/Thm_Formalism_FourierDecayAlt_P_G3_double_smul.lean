-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G3_double_smul
-- name    : Formalism.FourierDecayAlt.P.G3.double_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:39:04.133617+00:00
-- url     : https://prove2.me/theorems/a066527d-3e01-495c-b0c3-b037d03f7656
-- title:
--   G3: double smul
-- statement:
--   The G3 construction uses the double smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AffineChangeOfVariables.lean#L88-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AffineChangeOfVariables.lean#L88-L96

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G3

theorem Formalism.FourierDecayAlt.P.G3.double_smul (β : ℂ) (hβ : β ≠ 0) (κ : NNReal) (f : SchwartzMap ℂ ℂ) (w : ℂ) :
    ∫ ξ : ℂ, (∫ x : ℂ, f x * psi β (ξ * x) ∂(κ • (volume : Measure ℂ))) * psi β (w * ξ)
        ∂(κ • (volume : Measure ℂ)) =
      (((κ : ℝ) ^ 2 * ((‖β‖ / (2 * Real.pi)) ^ 2)⁻¹ : ℝ) : ℂ) * f (-w) := by sorry
