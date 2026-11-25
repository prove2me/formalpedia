-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_capelli_left_translation
-- name    : Formalism.FourierDecayAlt.P.capelli_left_translation
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:36:36.76642+00:00
-- url     : https://prove2.me/theorems/f6d0d079-7c35-5ddd-9217-230a0e3cccc9
-- title:
--   P: capelli left translation
-- statement:
--   The P construction uses the capelli left translation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L348-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L348-L348

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

theorem Formalism.FourierDecayAlt.P.capelli_left_translation : Formalism.FourierDecayAlt.JF.CVLeft := by sorry
