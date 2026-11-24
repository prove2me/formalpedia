-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_fourth_expansion_of_parts
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.fourth_expansion_of_parts
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:44.808795+00:00
-- url     : https://prove2.me/theorems/47ecd50b-758f-481f-abad-de377cdc1d2b
-- title:
--   Sign Antidiagonal: fourth expansion of parts
-- statement:
--   The Sign Antidiagonal construction uses the fourth expansion of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightDerivativeRulePsi.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightDerivativeRulePsi.lean#L22-L25

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.fourth_expansion_of_parts : ExpansionFourthCaseFromComponents := by sorry
