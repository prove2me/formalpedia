-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_midEmb_mul
-- name    : Formalism.FourierDecayAlt.P.S3x3.midEmb_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:23.068813+00:00
-- url     : https://prove2.me/theorems/66aa2572-2bb1-4fd1-a867-097ff05fd0cc
-- title:
--   S3x3: mid Emb mul
-- statement:
--   The S3x3 construction uses the mid Emb mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L200-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L200-L201

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

theorem Formalism.FourierDecayAlt.P.S3x3.midEmb_mul (a b : Matrix (Fin k) (Fin k) A) : midEmb (a * b) = midEmb a * midEmb b := by sorry
