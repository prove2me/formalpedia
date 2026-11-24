-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_det_RhE
-- name    : Formalism.FourierDecayAlt.P.Wd4.det_RhE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:21.447973+00:00
-- url     : https://prove2.me/theorems/c8584c00-b127-409c-8cd1-9576522eee7b
-- title:
--   Wd4: det Rh E
-- statement:
--   The Wd4 construction uses the det Rh E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L166-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L166-L178

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

theorem Formalism.FourierDecayAlt.P.Wd4.det_RhE (he : MU e) (D : K) (h0 : D ≠ 0) (h1 : D ≠ 1) :
    (RhE e (D + 1))ᵀ * YangianSpanCharacter.T.J B * RhE e D = ((D + 1) / D) • YangianSpanCharacter.T.J B ∧
      RhE e D * YangianSpanCharacter.T.J B * (RhE e (D + 1))ᵀ = ((D + 1) / D) • YangianSpanCharacter.T.J B := by sorry
