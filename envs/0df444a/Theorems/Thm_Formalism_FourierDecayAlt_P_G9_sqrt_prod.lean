-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G9_sqrt_prod
-- name    : Formalism.FourierDecayAlt.P.G9.sqrt_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:15.588056+00:00
-- url     : https://prove2.me/theorems/e6a3fcbe-281a-4726-a69b-c8434faebe3e
-- title:
--   G9: sqrt prod
-- statement:
--   The G9 construction uses the sqrt prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L195-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L195-L232

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9

theorem Formalism.FourierDecayAlt.P.G9.sqrt_prod (δ r : ℝ) (hδ : 0 < δ) :
    ((Real.pi : ℂ) / ((δ : ℂ) - r * Complex.I)) ^ (1 / 2 : ℂ) *
      ((Real.pi : ℂ) / ((δ : ℂ) + r * Complex.I)) ^ (1 / 2 : ℂ) =
      ((Real.pi / Real.sqrt (δ ^ 2 + r ^ 2) : ℝ) : ℂ) := by sorry
