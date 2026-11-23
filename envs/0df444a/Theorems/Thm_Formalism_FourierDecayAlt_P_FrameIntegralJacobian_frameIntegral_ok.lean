-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameIntegralJacobian_frameIntegral_ok
-- name    : Formalism.FourierDecayAlt.P.FrameIntegralJacobian.frameIntegral_ok
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:48.570327+00:00
-- url     : https://prove2.me/theorems/dc121323-49f7-4fe3-9f0a-0370248a0fa4
-- title:
--   Frame Integral Jacobian: frame Integral ok
-- statement:
--   The Frame Integral Jacobian construction uses the frame Integral ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameIntegralJacobian.lean#L207-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameIntegralJacobian.lean#L207-L223

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FrameIntegralJacobian
open Formalism.FourierDecayAlt.PairingProductCorollary

theorem Formalism.FourierDecayAlt.P.FrameIntegralJacobian.frameIntegral_ok : FrameIntegral := by sorry
