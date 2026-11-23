-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_det_mul_at
-- name    : Formalism.FourierDecayAlt.P.Wd4.det_mul_at
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:25.735128+00:00
-- url     : https://prove2.me/theorems/277a6ed2-2b4d-4f63-9398-64c12d14556f
-- title:
--   Wd4: det mul at
-- statement:
--   The Wd4 construction uses the det mul at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L256-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L256-L278

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

theorem Formalism.FourierDecayAlt.P.Wd4.det_mul_at (M N : K → M2 B) (q qN : K → K) (Y : K) (hM : DetAt M q Y) (hN : DetAt N qN Y)
    (hc : ∀ Y Y' i j k l, Commute (M Y i j) (N Y' k l)) :
    DetAt (fun Y => M Y * N Y) (fun Y => q Y * qN Y) Y := by sorry
