-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_jf_cVUnderIntOfParts_alt
-- name    : Formalism.FourierDecayAlt.P.JFxB.jf_cVUnderIntOfParts_alt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:41:25.386946+00:00
-- url     : https://prove2.me/theorems/8acb90cc-5786-5f4c-9f26-e0f321f9de49
-- title:
--   JFx B: jf c VUnder Int Of Parts alt
-- statement:
--   The JFx B construction uses the jf c VUnder Int Of Parts alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L356-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L356-L358

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

theorem Formalism.FourierDecayAlt.P.JFxB.jf_cVUnderIntOfParts_alt : Formalism.FourierDecayAlt.JF.CVUnderIntOfParts := by sorry
