-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_ybet_alg
-- name    : Formalism.FourierDecayAlt.P.Wd4.ybet_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:23.259745+00:00
-- url     : https://prove2.me/theorems/39ec475a-06f8-48d1-a31a-49b518ff3bd1
-- title:
--   Wd4: ybet alg
-- statement:
--   The Wd4 construction uses the ybet alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L91-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L91-L100

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

theorem Formalism.FourierDecayAlt.P.Wd4.ybet_alg {C : Type} [Ring C] [Algebra K C] (p12 q13 q23 : C) (d' d : K)
    (g1 : p12 * q13 = q23 * p12) (g2 : p12 * q23 = q13 * p12)
    (g3 : q13 * q23 = q13 * p12) (g4 : q23 * q13 = q23 * p12) :
    ((d - d') • (1 : C) - p12) * (d' • (1 : C) - q13) * (d • (1 : C) - q23) =
      (d • (1 : C) - q23) * (d' • (1 : C) - q13) * ((d - d') • (1 : C) - p12) := by sorry
