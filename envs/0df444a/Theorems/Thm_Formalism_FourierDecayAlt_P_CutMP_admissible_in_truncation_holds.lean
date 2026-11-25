-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_admissible_in_truncation_holds
-- name    : Formalism.FourierDecayAlt.P.CutMP.admissible_in_truncation_holds
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:27:53.18563+00:00
-- url     : https://prove2.me/theorems/64288f02-5001-4430-bc0a-0975a547fce4
-- title:
--   Cut MP: admissible in truncation holds
-- statement:
--   The Cut MP construction uses the admissible in truncation holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutAdm.lean#L7-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutAdm.lean#L7-L31

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutAdm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
open Formalism.FourierDecayAlt

theorem Formalism.FourierDecayAlt.P.CutMP.admissible_in_truncation_holds : AdmInCut := by sorry
