-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_rank_conj_mul
-- name    : Formalism.FourierDecayAlt.P.S3x5.rank_conj_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:11.569691+00:00
-- url     : https://prove2.me/theorems/6d56bcd4-384b-49be-a32e-95130ed92d77
-- title:
--   S3x5: rank conj mul
-- statement:
--   The S3x5 construction uses the rank conj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L970-L996
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L970-L996

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

theorem Formalism.FourierDecayAlt.P.S3x5.rank_conj_mul {n a : ℕ} (X : Matrix (Fin n) (Fin a) K) (hX : X.rank = a)
    (J : Matrix (Fin n) (Fin n) K) (hdJ : IsUnit J.det) : (Xᴴ * J).rank = a := by sorry
