-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_frame_jacobian_formula
-- name    : Formalism.FourierDecayAlt.P.frame_jacobian_formula
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:31:38.568066+00:00
-- url     : https://prove2.me/theorems/97cf8eea-2e3e-4980-8f96-d9f33ca8ebd3
-- title:
--   P: frame jacobian formula
-- statement:
--   The P construction uses the frame jacobian formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameIntegralJacobian.lean#L265-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameIntegralJacobian.lean#L265-L265

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

theorem Formalism.FourierDecayAlt.P.frame_jacobian_formula : Formalism.FourierDecayAlt.PairingProductCorollary.FrameJacobian := by sorry
