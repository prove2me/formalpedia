-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_omStable_statement
-- name    : Formalism.FourierDecayAlt.P.omStable_statement
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:33.490848+00:00
-- url     : https://prove2.me/theorems/809b0586-ebc2-4cc5-9949-2425609e102e
-- title:
--   P: om Stable statement
-- statement:
--   The P construction uses the om Stable statement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameLevelIndices.lean#L172-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameLevelIndices.lean#L172-L199

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

theorem Formalism.FourierDecayAlt.P.omStable_statement : Formalism.FourierDecayAlt.S3.OmStable := by sorry
