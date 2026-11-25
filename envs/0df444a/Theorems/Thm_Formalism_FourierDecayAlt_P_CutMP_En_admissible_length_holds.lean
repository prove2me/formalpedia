-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_En_admissible_length_holds
-- name    : Formalism.FourierDecayAlt.P.CutMP.En.admissible_length_holds
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:44:31.012879+00:00
-- url     : https://prove2.me/theorems/f7cb75cf-1600-5cd4-b71e-a2b77feb849b
-- title:
--   En: admissible length holds
-- statement:
--   The En construction uses the admissible length holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutEnAdmLen.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutEnAdmLen.lean#L7-L10

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnAdmLen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.En

theorem Formalism.FourierDecayAlt.P.CutMP.En.admissible_length_holds : AdmLen := by sorry
