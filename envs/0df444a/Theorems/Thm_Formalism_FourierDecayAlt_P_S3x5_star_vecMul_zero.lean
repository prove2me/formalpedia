-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_star_vecMul_zero
-- name    : Formalism.FourierDecayAlt.P.S3x5.star_vecMul_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:13.508798+00:00
-- url     : https://prove2.me/theorems/185fad3a-6957-4118-92bf-279a920cef18
-- title:
--   S3x5: star vec Mul zero
-- statement:
--   The S3x5 construction uses the star vec Mul zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L590-L595
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L590-L595

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix
variable {K : Type} [Field K] [Fintype K] [StarRing K]
omit [Fintype K]

theorem Formalism.FourierDecayAlt.P.S3x5.star_vecMul_zero {α κ : Type} [Fintype α] (M : Matrix α κ K) (u : α → K)
    (h : Mᴴ *ᵥ u = 0) : star u ᵥ* M = 0 := by sorry
