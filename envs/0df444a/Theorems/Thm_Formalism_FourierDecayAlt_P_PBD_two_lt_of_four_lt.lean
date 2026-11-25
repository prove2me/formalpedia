-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_two_lt_of_four_lt
-- name    : Formalism.FourierDecayAlt.P.PBD.two_lt_of_four_lt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:47:58.237423+00:00
-- url     : https://prove2.me/theorems/b80205a2-c1f8-54ba-9e91-fc1d4fc62e56
-- title:
--   PBD: two lt of four lt
-- statement:
--   The PBD construction uses the two lt of four lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RoomOffGridSymmetric.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RoomOffGridSymmetric.lean#L104-L107

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

theorem Formalism.FourierDecayAlt.P.PBD.two_lt_of_four_lt {y p : ℝ} (h : 4 < |y - p|) : 2 < |y + 1 - p| := by sorry
