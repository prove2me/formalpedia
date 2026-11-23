-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_isUnit_det_of_isS
-- name    : Formalism.FourierDecayAlt.P.S3x3.isUnit_det_of_isS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:52.243138+00:00
-- url     : https://prove2.me/theorems/3ebb2771-ca85-4c05-b2f2-365942e69711
-- title:
--   S3x3: is Unit det of is S
-- statement:
--   The S3x3 construction uses the is Unit det of is S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L481-L484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L481-L484

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x3
open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
variable {A : Type} [CommRing A] {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x3.isUnit_det_of_isS {x : Matrix (Idx r k) (Idx r k) A} (hx : IsS x) : IsUnit x.det := by sorry
