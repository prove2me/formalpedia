-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_roots_outside_jointly
-- name    : Formalism.FourierDecayAlt.P.roots_outside_jointly
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:06:43.888681+00:00
-- url     : https://prove2.me/theorems/d22d329d-0258-4232-98a1-8f0aec8b63ca
-- title:
--   P: roots outside jointly
-- statement:
--   The P construction uses the roots outside jointly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RhoAntitoneOfInterlacing.lean#L140-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RhoAntitoneOfInterlacing.lean#L140-L151

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

theorem Formalism.FourierDecayAlt.P.roots_outside_jointly : C7.RootsOutJoint := by sorry
