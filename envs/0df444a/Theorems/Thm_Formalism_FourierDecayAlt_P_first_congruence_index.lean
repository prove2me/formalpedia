-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_first_congruence_index
-- name    : Formalism.FourierDecayAlt.P.first_congruence_index
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:32:25.104353+00:00
-- url     : https://prove2.me/theorems/c0a3e69e-7c2b-4eb5-be00-ad81600a21a5
-- title:
--   P: first congruence index
-- statement:
--   The P construction uses the first congruence index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameLevelIndices.lean#L139-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameLevelIndices.lean#L139-L154

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
open Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.FrameLevelIndices

theorem Formalism.FourierDecayAlt.P.first_congruence_index : Formalism.FourierDecayAlt.S3.CongruenceLevelIndex := by sorry
