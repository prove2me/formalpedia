-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_ybe_alg
-- name    : Formalism.FourierDecayAlt.P.Wd4.ybe_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:30.6138+00:00
-- url     : https://prove2.me/theorems/bae622d7-0627-4691-a321-4e5bed8ac728
-- title:
--   Wd4: ybe alg
-- statement:
--   The Wd4 construction uses the ybe alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L78-L89

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

theorem Formalism.FourierDecayAlt.P.Wd4.ybe_alg {C : Type} [Ring C] [Algebra K C] (p12 p13 p23 : C) (u v : K)
    (h1 : p13 * p23 = p12 * p13) (h2 : p23 * p12 = p12 * p13)
    (h3 : p23 * p13 = p12 * p23) (h4 : p13 * p12 = p12 * p23) :
    ((u - v) • (1 : C) - p12) * (u • (1 : C) - p13) * (v • (1 : C) - p23) =
      (v • (1 : C) - p23) * (u • (1 : C) - p13) * ((u - v) • (1 : C) - p12) := by sorry
