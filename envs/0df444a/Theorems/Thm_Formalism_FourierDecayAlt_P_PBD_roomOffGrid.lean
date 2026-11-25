-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_roomOffGrid
-- name    : Formalism.FourierDecayAlt.P.PBD.roomOffGrid
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:39:44.477463+00:00
-- url     : https://prove2.me/theorems/fec39aed-10c9-55d4-ab2a-50f62f79fbaf
-- title:
--   PBD: room Off Grid
-- statement:
--   The PBD construction uses the room Off Grid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RoomOffGridSymmetric.lean#L117-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RoomOffGridSymmetric.lean#L117-L160

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField

theorem Formalism.FourierDecayAlt.P.PBD.roomOffGrid : RoomOffGrid := by sorry
