-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_general_mass_of_split
-- name    : Formalism.FourierDecayAlt.P.general_mass_of_split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:38:40.38079+00:00
-- url     : https://prove2.me/theorems/6d101685-625b-4934-909f-d6b6f887ec15
-- title:
--   P: general mass of split
-- statement:
--   The P construction uses the general mass of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L1141-L1141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L1141-L1141

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt

theorem Formalism.FourierDecayAlt.P.general_mass_of_split : Formalism.FourierDecayAlt.PN.GenMassOfSplit := by sorry
