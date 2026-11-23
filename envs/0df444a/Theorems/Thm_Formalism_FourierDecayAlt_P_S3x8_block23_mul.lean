-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block23_mul
-- name    : Formalism.FourierDecayAlt.P.S3x8.block23_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:22.373845+00:00
-- url     : https://prove2.me/theorems/01199f64-408b-4ef8-a1d7-aa6faf61b81a
-- title:
--   S3x8: block23 mul
-- statement:
--   The S3x8 construction uses the block23 mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L468-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L468-L471

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]

theorem Formalism.FourierDecayAlt.P.S3x8.block23_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b23 (x * y) = b21 x * b13 y + b22 x * b23 y + b23 x * b33 y := by sorry
