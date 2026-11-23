-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_det_RhtE
-- name    : Formalism.FourierDecayAlt.P.Wd4.det_RhtE
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:18.289794+00:00
-- url     : https://prove2.me/theorems/988a7b1d-83c4-4314-a837-c40880245e58
-- title:
--   Wd4: det Rht E
-- statement:
--   The Wd4 construction uses the det Rht E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L180-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L180-L197

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

theorem Formalism.FourierDecayAlt.P.Wd4.det_RhtE (he : MU e) (d : K) (h1 : d ≠ 1) (h2 : d - 1 ≠ 1) :
    (RhtE e (d - 1))ᵀ * YangianSpanCharacter.T.J B * RhtE e d = (d / (d - 1)) • YangianSpanCharacter.T.J B ∧
      RhtE e d * YangianSpanCharacter.T.J B * (RhtE e (d - 1))ᵀ = (d / (d - 1)) • YangianSpanCharacter.T.J B := by sorry
