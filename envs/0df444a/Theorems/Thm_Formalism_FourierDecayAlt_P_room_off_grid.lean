-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_room_off_grid
-- name    : Formalism.FourierDecayAlt.P.room_off_grid
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:38:10.467844+00:00
-- url     : https://prove2.me/theorems/3f4d183a-2a03-556b-8524-e58cb864901c
-- title:
--   P: room off grid
-- statement:
--   The P construction uses the room off grid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RoomOffGridSymmetric.lean#L191-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RoomOffGridSymmetric.lean#L191-L191

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem Formalism.FourierDecayAlt.P.room_off_grid : Formalism.FourierDecayAlt.P.PBD.RoomOffGrid := by sorry
