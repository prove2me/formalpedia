-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_rank_of_gram
-- name    : Formalism.FourierDecayAlt.P.S3x5.rank_of_gram
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:44.492867+00:00
-- url     : https://prove2.me/theorems/6e0f8e49-8fcb-46ea-a051-28d8b8b40aaf
-- title:
--   S3x5: rank of gram
-- statement:
--   The S3x5 construction uses the rank of gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L787-L793
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L787-L793

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
open Matrix Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K] [StarRing K]
omit [Fintype K]

theorem Formalism.FourierDecayAlt.P.S3x5.rank_of_gram {ν α : Type} [Fintype ν] [DecidableEq ν] [Fintype α] [DecidableEq α]
    (J : Matrix ν ν K) (T : Matrix α α K) (hdT : IsUnit T.det) (X : Matrix ν α K)
    (h : Xᴴ * J * X = T) : X.rank = Fintype.card α := by sorry
