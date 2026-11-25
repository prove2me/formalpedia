-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_pn_zpow_form
-- name    : Formalism.FourierDecayAlt.P.pn_zpow_form
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:36:11.254805+00:00
-- url     : https://prove2.me/theorems/2a0e58e1-04c5-5d77-b916-9b97e9809873
-- title:
--   P: pn zpow form
-- statement:
--   The P construction uses the pn zpow form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L1127-L1127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L1127-L1127

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

theorem Formalism.FourierDecayAlt.P.pn_zpow_form : Formalism.FourierDecayAlt.PN.ZpowForm := by sorry
