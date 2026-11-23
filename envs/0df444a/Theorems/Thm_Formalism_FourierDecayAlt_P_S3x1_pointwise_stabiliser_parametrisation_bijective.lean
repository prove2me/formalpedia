-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_pointwise_stabiliser_parametrisation_bijective
-- name    : Formalism.FourierDecayAlt.P.S3x1.pointwise_stabiliser_parametrisation_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:05.792915+00:00
-- url     : https://prove2.me/theorems/e8d413da-197e-4cf2-9878-08c88a4af9eb
-- title:
--   S3x1: pointwise stabiliser parametrisation bijective
-- statement:
--   The S3x1 construction uses the pointwise stabiliser parametrisation bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointwiseStabiliserParametrisationBijective.lean#L599-L638
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointwiseStabiliserParametrisationBijective.lean#L599-L638

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x1
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x1.pointwise_stabiliser_parametrisation_bijective : Function.Bijective (pointwiseStabiliserParametrisation (A := A) (r := r) (k := k)) := by sorry
