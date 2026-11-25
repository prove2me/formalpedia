-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_roots_outside_of_parts
-- name    : Formalism.FourierDecayAlt.P.roots_outside_of_parts
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:44:35.836919+00:00
-- url     : https://prove2.me/theorems/414b0cc0-0ae5-42c2-831d-62513ef24500
-- title:
--   P: roots outside of parts
-- statement:
--   The P construction uses the roots outside of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RhoAntitoneOfInterlacing.lean#L153-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RhoAntitoneOfInterlacing.lean#L153-L153

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RhoAntitoneOfInterlacing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.roots_outside_of_parts : C7.RootsOutOfParts := by sorry
