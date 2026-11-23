-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_parMap_bij
-- name    : Formalism.FourierDecayAlt.P.S3x1.parMap_bij
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:00.061806+00:00
-- url     : https://prove2.me/theorems/e59c6244-e105-42ba-b059-d5ce04270c5e
-- title:
--   S3x1: par Map bij
-- statement:
--   The S3x1 construction uses the par Map bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointwiseStabiliserParametrisationBijective.lean#L523-L555
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointwiseStabiliserParametrisationBijective.lean#L523-L555

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
variable {A : Type} [CommRing A]
variable {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x1.parMap_bij (P : Matrix (Fin k) (Fin k) A → Prop) : Function.Bijective (parMap (r := r) P) := by sorry
