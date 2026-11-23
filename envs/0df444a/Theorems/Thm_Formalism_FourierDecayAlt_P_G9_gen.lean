-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G9_gen
-- name    : Formalism.FourierDecayAlt.P.G9.gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:34.612897+00:00
-- url     : https://prove2.me/theorems/bfc241e4-8142-42f6-a472-8415ce4e8e33
-- title:
--   G9: gen
-- statement:
--   The G9 construction uses the gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L269-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L269-L283

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

theorem Formalism.FourierDecayAlt.P.G9.gen (δ : ℝ) (γ : ℂ) (hδ : 0 < δ) :
    ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * Complex.exp (Complex.I * (((γ * w ^ 2).re : ℝ) : ℂ)) =
      ((Real.pi / Real.sqrt (δ ^ 2 + ‖γ‖ ^ 2) : ℝ) : ℂ) := by sorry
