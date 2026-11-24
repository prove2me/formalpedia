-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_det2
-- name    : Formalism.FourierDecayAlt.P.Wd4.det2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:23.810854+00:00
-- url     : https://prove2.me/theorems/4de9c9df-1002-40f3-964d-812a44787c34
-- title:
--   Wd4: det2
-- statement:
--   The Wd4 construction uses the det2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L149-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L149-L154

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

theorem Formalism.FourierDecayAlt.P.Wd4.det2 (he : MU e) (D : K) :
    (D • (1 : M2 B) - PE e) * YangianSpanCharacter.T.J B * ((D + 1) • (1 : M2 B) - QE e) =
      ((D + 1) * (D - 1)) • YangianSpanCharacter.T.J B := by sorry
