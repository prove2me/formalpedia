-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RootChangeOfVariables_ae_ne_zero
-- name    : Formalism.FourierDecayAlt.P.RootChangeOfVariables.ae_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:47:42.510334+00:00
-- url     : https://prove2.me/theorems/743af490-1b62-4451-a475-6dc2eccc9491
-- title:
--   Root Change Of Variables: ae ne zero
-- statement:
--   The Root Change Of Variables construction uses the ae ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JacobianAeNonzero.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JacobianAeNonzero.lean#L19-L22

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

theorem Formalism.FourierDecayAlt.P.RootChangeOfVariables.ae_ne_zero : ∀ᵐ D : ℂ, D ∈ {D : ℂ | D ≠ 0} := by sorry
