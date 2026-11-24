-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_exists_singular_maximal_vector
-- name    : Formalism.FourierDecayAlt.P.exists_singular_maximal_vector
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:52:47.946519+00:00
-- url     : https://prove2.me/theorems/5e765000-cffc-4769-87fd-d6f99eeca787
-- title:
--   P: exists singular maximal vector
-- statement:
--   The P construction uses the exists singular maximal vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommonEigenvectors.lean#L97-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommonEigenvectors.lean#L97-L142

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommonEigenvectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr CommonEigenvectors

theorem Formalism.FourierDecayAlt.P.exists_singular_maximal_vector : Qr.ExistsSingMax := by sorry
