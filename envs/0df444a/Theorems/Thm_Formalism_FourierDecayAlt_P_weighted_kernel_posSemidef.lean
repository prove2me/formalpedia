-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_weighted_kernel_posSemidef
-- name    : Formalism.FourierDecayAlt.P.weighted_kernel_posSemidef
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:35:16.146546+00:00
-- url     : https://prove2.me/theorems/84da8c29-c870-51a5-be54-c49c9acb87de
-- title:
--   P: weighted kernel pos Semidef
-- statement:
--   The P construction uses the weighted kernel pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameIntegralJacobian.lean#L262-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameIntegralJacobian.lean#L262-L262

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

theorem Formalism.FourierDecayAlt.P.weighted_kernel_posSemidef : Formalism.FourierDecayAlt.PairingProductCorollary.WeightedKernelPSD := by sorry
