-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameLevelIndices_densityProduct_eq_prod_range
-- name    : Formalism.FourierDecayAlt.P.FrameLevelIndices.densityProduct_eq_prod_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:25.537683+00:00
-- url     : https://prove2.me/theorems/93209123-5ca0-47c5-bed3-dff417519ae4
-- title:
--   Frame Level Indices: density Product eq prod range
-- statement:
--   The Frame Level Indices construction uses the density Product eq prod range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameLevelIndices.lean#L57-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameLevelIndices.lean#L57-L79

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameLevelIndices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FrameLevelIndices
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_one)
open Formalism.FourierDecayAlt.S3

theorem Formalism.FourierDecayAlt.P.FrameLevelIndices.densityProduct_eq_prod_range (q a m : ℕ) :
    densP 1 q ((a : ℤ) + 1) ((a + m : ℕ) : ℤ) = ∏ x ∈ range m, fac q (a + x) := by sorry
