-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RootChangeOfVariables_jac
-- name    : Formalism.FourierDecayAlt.P.RootChangeOfVariables.jac
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:47:46.109053+00:00
-- url     : https://prove2.me/theorems/eba3939c-459e-41ed-808e-4adde2d05aba
-- title:
--   Root Change Of Variables: jac
-- statement:
--   The Root Change Of Variables construction uses the jac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JacobianAeNonzero.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JacobianAeNonzero.lean#L11-L17

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourthWeightDensityOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JacobianAeNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt MeasureTheory
open scoped ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.RootChangeOfVariables

theorem Formalism.FourierDecayAlt.P.RootChangeOfVariables.jac (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ : ℂ →L[ℝ] ℂ).det = Complex.normSq c := by sorry
