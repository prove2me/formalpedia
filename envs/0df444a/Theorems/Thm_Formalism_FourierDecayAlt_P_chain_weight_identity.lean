-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_chain_weight_identity
-- name    : Formalism.FourierDecayAlt.P.chain_weight_identity
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:29:42.609812+00:00
-- url     : https://prove2.me/theorems/2cb6f672-6e67-4989-ad18-bac51fff3446
-- title:
--   P: chain weight identity
-- statement:
--   The P construction uses the chain weight identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderChainWeights.lean#L128-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderChainWeights.lean#L128-L165

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

theorem Formalism.FourierDecayAlt.P.chain_weight_identity : Formalism.FourierDecayAlt.S3.ChainIdentity := by sorry
