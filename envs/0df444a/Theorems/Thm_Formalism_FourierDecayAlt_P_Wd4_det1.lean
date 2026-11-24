-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_det1
-- name    : Formalism.FourierDecayAlt.P.Wd4.det1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:20.139329+00:00
-- url     : https://prove2.me/theorems/e8c924dc-fca6-4198-9c68-d20d29f719cd
-- title:
--   Wd4: det1
-- statement:
--   The Wd4 construction uses the det1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L142-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L142-L147

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

theorem Formalism.FourierDecayAlt.P.Wd4.det1 (he : MU e) (D : K) :
    ((D + 1) • (1 : M2 B) - QE e) * YangianSpanCharacter.T.J B * (D • (1 : M2 B) - PE e) =
      ((D + 1) * (D - 1)) • YangianSpanCharacter.T.J B := by sorry
