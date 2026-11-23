-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameIntegralJacobian_gaExponent_ok
-- name    : Formalism.FourierDecayAlt.P.FrameIntegralJacobian.gaExponent_ok
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:47.051499+00:00
-- url     : https://prove2.me/theorems/3ee7b096-9e0d-4d49-91ce-cec3e6916d36
-- title:
--   Frame Integral Jacobian: ga Exponent ok
-- statement:
--   The Frame Integral Jacobian construction uses the ga Exponent ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameIntegralJacobian.lean#L110-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameIntegralJacobian.lean#L110-L130

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

theorem Formalism.FourierDecayAlt.P.FrameIntegralJacobian.gaExponent_ok : GaExponent := by sorry
