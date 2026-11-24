-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_theta_bessel_commute_of_parts
-- name    : Formalism.FourierDecayAlt.P.theta_bessel_commute_of_parts
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:34:09.591498+00:00
-- url     : https://prove2.me/theorems/7d2934bf-3da0-495b-8ec0-ced01578bf28
-- title:
--   P: theta bessel commute of parts
-- statement:
--   The P construction uses the theta bessel commute of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordIntegralScaling.lean#L56-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordIntegralScaling.lean#L56-L104

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.theta_bessel_commute_of_parts : Formalism.FourierDecayAlt.JF.JThetaOfParts := by sorry
