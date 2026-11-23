-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G9_core
-- name    : Formalism.FourierDecayAlt.P.G9.core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:29.860839+00:00
-- url     : https://prove2.me/theorems/9371b705-2e78-4e03-a82c-9e4b7571e19a
-- title:
--   G9: core
-- statement:
--   The G9 construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L234-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L234-L256

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

theorem Formalism.FourierDecayAlt.P.G9.core (δ r : ℝ) (hδ : 0 < δ) :
    ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * Complex.exp (Complex.I * ((r * (w ^ 2).re : ℝ) : ℂ)) =
      ((Real.pi / Real.sqrt (δ ^ 2 + r ^ 2) : ℝ) : ℂ) := by sorry
