-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameLevelIndices_gl_real
-- name    : Formalism.FourierDecayAlt.P.FrameLevelIndices.gl_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:19.269124+00:00
-- url     : https://prove2.me/theorems/122365f0-4b84-42db-ac61-34af872aa761
-- title:
--   Frame Level Indices: gl real
-- statement:
--   The Frame Level Indices construction uses the gl real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameLevelIndices.lean#L81-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameLevelIndices.lean#L81-L97

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

theorem Formalism.FourierDecayAlt.P.FrameLevelIndices.gl_real (q n : ℕ) (hq : 1 ≤ q) :
    ((∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) : ℕ) : ℝ) = (q : ℝ) ^ (n * n) * ∏ x ∈ range n, fac q x := by sorry
