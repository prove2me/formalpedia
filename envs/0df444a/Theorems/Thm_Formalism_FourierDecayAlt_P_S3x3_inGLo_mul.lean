-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_inGLo_mul
-- name    : Formalism.FourierDecayAlt.P.S3x3.inGLo_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:27.729129+00:00
-- url     : https://prove2.me/theorems/33bbe806-6b76-494e-92f5-d157535c90ab
-- title:
--   S3x3: in GLo mul
-- statement:
--   The S3x3 construction uses the in GLo mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L288-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L288-L292

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
variable (o : Type) [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]

theorem Formalism.FourierDecayAlt.P.S3x3.inGLo_mul {ι : Type} [Fintype ι] [DecidableEq ι] {x y : Matrix ι ι k0} (hx : InGLo o x)
    (hy : InGLo o y) : InGLo o (x * y) := by sorry
