-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_frame_module_of_word
-- name    : Formalism.FourierDecayAlt.P.frame_module_of_word
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:46:49.365798+00:00
-- url     : https://prove2.me/theorems/0b79cbc4-0b7f-4657-8a6b-4ba520d4152b
-- title:
--   P: frame module of word
-- statement:
--   The P construction uses the frame module of word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuasiDeterminantFromEntries.lean#L362-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuasiDeterminantFromEntries.lean#L362-L384

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.frame_module_of_word : WordJoint := by sorry
