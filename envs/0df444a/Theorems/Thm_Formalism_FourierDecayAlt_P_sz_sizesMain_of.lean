-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_sz_sizesMain_of
-- name    : Formalism.FourierDecayAlt.P.sz_sizesMain_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:04.79135+00:00
-- url     : https://prove2.me/theorems/c216c1f7-8c05-4ea2-9de0-20a46d76bf82
-- title:
--   P: sz sizes Main of
-- statement:
--   The P construction uses the sz sizes Main of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SixteenMulLeTwoPow.lean#L113-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SixteenMulLeTwoPow.lean#L113-L333

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SixteenMulLeTwoPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz9
set_option maxHeartbeats 1000000

theorem Formalism.FourierDecayAlt.P.sz_sizesMain_of (hCorA : CorA) (hBeta : BetaOnCut) (hAZ : AZeroBound)
    (hIL : Interlacing) (hLA : LamAnti) (hTP : ThresholdProducts) (hTL : ThetaLower) (hThP : ThetaPower)
    (hFS : FinalSmall) : SizesMain := by sorry
