-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_detAt_iff
-- name    : Formalism.FourierDecayAlt.P.Wd4.detAt_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:16:12.63479+00:00
-- url     : https://prove2.me/theorems/13ceb993-d89e-43c2-9641-c8a00e8d904c
-- title:
--   Wd4: det At iff
-- statement:
--   The Wd4 construction uses the det At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L251-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L251-L254

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

theorem Formalism.FourierDecayAlt.P.Wd4.detAt_iff (M : K → M2 B) (q : K → K) (Y : K) :
    DetAt M q Y ↔ (M (Y + 1))ᵀ * YangianSpanCharacter.T.J B * M Y = q Y • YangianSpanCharacter.T.J B ∧
      M Y * YangianSpanCharacter.T.J B * (M (Y + 1))ᵀ = q Y • YangianSpanCharacter.T.J B := by sorry
