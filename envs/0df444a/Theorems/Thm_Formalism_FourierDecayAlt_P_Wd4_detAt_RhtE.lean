-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_detAt_RhtE
-- name    : Formalism.FourierDecayAlt.P.Wd4.detAt_RhtE
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:54.393794+00:00
-- url     : https://prove2.me/theorems/d62f72cb-f03d-45d1-a0e8-b7eebb87f045
-- title:
--   Wd4: det At Rht E
-- statement:
--   The Wd4 construction uses the det At Rht E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L291-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L291-L299

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd4
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.W
variable {K B : Type} [Field K] [Ring B] [Algebra K B]
variable {e : Fin 2 → Fin 2 → B}

theorem Formalism.FourierDecayAlt.P.Wd4.detAt_RhtE (he : MU e) (Yb Y : K) (h1 : Yb - Y ≠ 1) (h2 : Yb - (Y + 1) ≠ 1) :
    DetAt (fun Y => RhtE e (Yb - Y)) (fun Y => (Yb - Y) / (Yb - Y - 1)) Y := by sorry
