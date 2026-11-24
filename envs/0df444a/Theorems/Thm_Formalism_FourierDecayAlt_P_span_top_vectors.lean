-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_span_top_vectors
-- name    : Formalism.FourierDecayAlt.P.span_top_vectors
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:53:07.831826+00:00
-- url     : https://prove2.me/theorems/f2db18d7-6fc1-4b16-8104-faebb5cfc729
-- title:
--   P: span top vectors
-- statement:
--   The P construction uses the span top vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L212-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L212-L295

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

theorem Formalism.FourierDecayAlt.P.span_top_vectors : Qr.SpanTop := by sorry
