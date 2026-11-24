-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_span_singular_vectors
-- name    : Formalism.FourierDecayAlt.P.span_singular_vectors
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:51:05.731663+00:00
-- url     : https://prove2.me/theorems/6c2d13b2-d2b0-463c-ad48-d4db62ee69dd
-- title:
--   P: span singular vectors
-- statement:
--   The P construction uses the span singular vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L297-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L297-L387

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
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
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr ClosureOperators

theorem Formalism.FourierDecayAlt.P.span_singular_vectors : Qr.SpanSing := by sorry
