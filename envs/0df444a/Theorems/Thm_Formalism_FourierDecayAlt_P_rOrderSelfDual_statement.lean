-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_rOrderSelfDual_statement
-- name    : Formalism.FourierDecayAlt.P.rOrderSelfDual_statement
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:34:57.17915+00:00
-- url     : https://prove2.me/theorems/c324fa77-e87f-4dc8-8665-700697b39ce6
-- title:
--   P: r Order Self Dual statement
-- statement:
--   The P construction uses the r Order Self Dual statement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderChainWeights.lean#L79-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderChainWeights.lean#L79-L126

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderChainWeights
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset MeasureTheory
open Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.OrderChainWeights
open scoped ENNReal

theorem Formalism.FourierDecayAlt.P.rOrderSelfDual_statement : Formalism.FourierDecayAlt.S3.ROrderSelfDual := by sorry
