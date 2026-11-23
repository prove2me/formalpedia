-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_ext9
-- name    : Formalism.FourierDecayAlt.P.S3x1.ext9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:21.768926+00:00
-- url     : https://prove2.me/theorems/3a7a83f1-4142-4cf1-9c4f-1e1ab7cb9967
-- title:
--   S3x1: ext9
-- statement:
--   The S3x1 construction uses the ext9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointwiseStabiliserParametrisationBijective.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointwiseStabiliserParametrisationBijective.lean#L16-L29

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
variable {A : Type} {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x1.ext9 {x y : Matrix (Idx r k) (Idx r k) A} (h11 : b11 x = b11 y) (h12 : b12 x = b12 y)
    (h13 : b13 x = b13 y) (h21 : b21 x = b21 y) (h22 : b22 x = b22 y) (h23 : b23 x = b23 y)
    (h31 : b31 x = b31 y) (h32 : b32 x = b32 y) (h33 : b33 x = b33 y) : x = y := by sorry
