-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_roomOffGridS
-- name    : Formalism.FourierDecayAlt.P.PBD.roomOffGridS
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:47:02.741346+00:00
-- url     : https://prove2.me/theorems/5e03b571-66ec-4207-97e5-998d6bcf97c3
-- title:
--   PBD: room Off Grid S
-- statement:
--   The PBD construction uses the room Off Grid S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RoomOffGridSymmetric.lean#L172-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RoomOffGridSymmetric.lean#L172-L187

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

theorem Formalism.FourierDecayAlt.P.PBD.roomOffGridS : RoomOffGridS := by sorry
