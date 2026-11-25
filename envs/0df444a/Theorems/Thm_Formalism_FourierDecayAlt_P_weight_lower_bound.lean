-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_weight_lower_bound
-- name    : Formalism.FourierDecayAlt.P.weight_lower_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:35:33.542898+00:00
-- url     : https://prove2.me/theorems/798de2b9-5d32-44d1-94d5-9f715f35794f
-- title:
--   P: weight lower bound
-- statement:
--   The P construction uses the weight lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameIntegralJacobian.lean#L254-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameIntegralJacobian.lean#L254-L254

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section

theorem Formalism.FourierDecayAlt.P.weight_lower_bound : Formalism.FourierDecayAlt.PairingProductCorollary.WeightLower := by sorry
