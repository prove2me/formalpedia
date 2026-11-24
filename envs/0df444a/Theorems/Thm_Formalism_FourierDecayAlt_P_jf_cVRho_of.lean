-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_jf_cVRho_of
-- name    : Formalism.FourierDecayAlt.P.jf_cVRho_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:25:21.906127+00:00
-- url     : https://prove2.me/theorems/5f7d1a60-4a93-4c7c-8eaf-60710770970f
-- title:
--   P: jf c VRho of
-- statement:
--   The P construction uses the jf c VRho of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L366-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L366-L367

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section

theorem Formalism.FourierDecayAlt.P.jf_cVRho_of : Formalism.FourierDecayAlt.P.JFxB.CapAdInv → Formalism.FourierDecayAlt.JF.CVRho := by sorry
