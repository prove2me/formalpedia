-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameLevelIndices_card_GL_idx
-- name    : Formalism.FourierDecayAlt.P.FrameLevelIndices.card_GL_idx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:19.300168+00:00
-- url     : https://prove2.me/theorems/3df49af3-8583-4116-aad1-b4bb514fbe91
-- title:
--   Frame Level Indices: card GL idx
-- statement:
--   The Frame Level Indices construction uses the card GL idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameLevelIndices.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameLevelIndices.lean#L99-L102

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

theorem Formalism.FourierDecayAlt.P.FrameLevelIndices.card_GL_idx (K : Type) [Field K] [Fintype K] (r k : ℕ) :
    Nat.card (GL (Idx r k) K) = Nat.card (GL (Fin (k + 2 * r + 1)) K) := by sorry
