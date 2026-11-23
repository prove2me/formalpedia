-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G3_double_vol
-- name    : Formalism.FourierDecayAlt.P.G3.double_vol
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:23.501695+00:00
-- url     : https://prove2.me/theorems/2d0097bb-0dbb-4952-9f6f-6aea601a3d40
-- title:
--   G3: double vol
-- statement:
--   The G3 construction uses the double vol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AffineChangeOfVariables.lean#L67-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AffineChangeOfVariables.lean#L67-L86

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

theorem Formalism.FourierDecayAlt.P.G3.double_vol (β : ℂ) (hβ : β ≠ 0) (f : SchwartzMap ℂ ℂ) (w : ℂ) :
    ∫ ξ : ℂ, (∫ x : ℂ, f x * psi β (ξ * x)) * psi β (w * ξ) =
      (((‖β‖ / (2 * Real.pi)) ^ 2)⁻¹ : ℝ) • f (-w) := by sorry
