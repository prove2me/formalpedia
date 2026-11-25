-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_jf_cVUnderInt_of
-- name    : Formalism.FourierDecayAlt.P.jf_cVUnderInt_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:35:32.660303+00:00
-- url     : https://prove2.me/theorems/30f7fe98-3016-5b07-bbc9-7f571ecc1337
-- title:
--   P: jf c VUnder Int of
-- statement:
--   The P construction uses the jf c VUnder Int of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L360-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L360-L361

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

theorem Formalism.FourierDecayAlt.P.jf_cVUnderInt_of : Formalism.FourierDecayAlt.JF.JWords → Formalism.FourierDecayAlt.JF.RwRho → Formalism.FourierDecayAlt.JF.CVUnderInt := by sorry
