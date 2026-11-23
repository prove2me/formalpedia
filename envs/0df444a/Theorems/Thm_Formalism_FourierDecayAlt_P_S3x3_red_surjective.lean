-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_red_surjective
-- name    : Formalism.FourierDecayAlt.P.S3x3.red_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:54:13.402382+00:00
-- url     : https://prove2.me/theorems/4eb9c584-89bc-4b97-bf5f-25df69f2f0da
-- title:
--   S3x3: red surjective
-- statement:
--   The S3x3 construction uses the red surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L413-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L413-L426

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

theorem Formalism.FourierDecayAlt.P.S3x3.red_surjective (o : Type) [CommRing o] [IsLocalRing o] (ι : Type) [Fintype ι]
    [DecidableEq ι] : Function.Surjective (red o ι) := by sorry
