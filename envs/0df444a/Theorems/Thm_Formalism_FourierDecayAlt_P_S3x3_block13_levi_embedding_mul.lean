-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block13_levi_embedding_mul
-- name    : Formalism.FourierDecayAlt.P.S3x3.block13_levi_embedding_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:36:04.777569+00:00
-- url     : https://prove2.me/theorems/16fbe941-9d80-4e3d-bb0d-414b01ff69ce
-- title:
--   S3x3: block13 levi embedding mul
-- statement:
--   The S3x3 construction uses the block13 levi embedding mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L166-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L166-L168

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
variable {A : Type} {r k : ℕ}
variable [CommRing A]

theorem Formalism.FourierDecayAlt.P.S3x3.block13_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b13 (hEmb r h * x) = b13 x := by sorry
