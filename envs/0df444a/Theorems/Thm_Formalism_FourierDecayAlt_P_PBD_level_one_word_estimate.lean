-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_level_one_word_estimate
-- name    : Formalism.FourierDecayAlt.P.PBD.level_one_word_estimate
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:18.88415+00:00
-- url     : https://prove2.me/theorems/57fc41fc-b47d-5d65-bfe6-955d63058d7b
-- title:
--   PBD: level one word estimate
-- statement:
--   The PBD construction uses the level one word estimate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelOneWordEstimate.lean#L89-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelOneWordEstimate.lean#L89-L103

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelOneWordEstimate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd

theorem Formalism.FourierDecayAlt.P.PBD.level_one_word_estimate : LevelOneWordEstimate := by sorry
