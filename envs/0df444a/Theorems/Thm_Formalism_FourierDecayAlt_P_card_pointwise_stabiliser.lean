-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_card_pointwise_stabiliser
-- name    : Formalism.FourierDecayAlt.P.card_pointwise_stabiliser
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:34.014584+00:00
-- url     : https://prove2.me/theorems/d2b89903-40a7-4005-a657-ee2eabbe7822
-- title:
--   P: card pointwise stabiliser
-- statement:
--   The P construction uses the card pointwise stabiliser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointwiseStabiliserParametrisationBijective.lean#L717-L724
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointwiseStabiliserParametrisationBijective.lean#L717-L724

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism.FourierDecayAlt.P.S3x1

theorem Formalism.FourierDecayAlt.P.card_pointwise_stabiliser : Formalism.FourierDecayAlt.S3.StabiliserIndexFinite := by sorry
