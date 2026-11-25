-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_instance_sizes
-- name    : Formalism.FourierDecayAlt.P.instance_sizes
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:32:35.894435+00:00
-- url     : https://prove2.me/theorems/fae09f2e-1c8c-49d7-bb95-aeba7c6b1b66
-- title:
--   P: instance sizes
-- statement:
--   The P construction uses the instance sizes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SupremumAIsMajorant.lean#L136-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SupremumAIsMajorant.lean#L136-L307

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx5

theorem Formalism.FourierDecayAlt.P.instance_sizes : InstSizes := by sorry
