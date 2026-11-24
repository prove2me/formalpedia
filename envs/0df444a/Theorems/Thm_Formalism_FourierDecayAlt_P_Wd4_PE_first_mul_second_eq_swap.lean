-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_PE_first_mul_second_eq_swap
-- name    : Formalism.FourierDecayAlt.P.Wd4.PE_first_mul_second_eq_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:01.847437+00:00
-- url     : https://prove2.me/theorems/6fc944d0-35c5-4d9b-8c30-720e0113cd50
-- title:
--   Wd4: PE first mul second eq swap
-- statement:
--   The Wd4 construction uses the PE first mul second eq swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L58-L61

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

theorem Formalism.FourierDecayAlt.P.Wd4.PE_first_mul_second_eq_swap (he : MU e) : E1 (PE e) * E2 (PE e) = Pf B * E1 (PE e) := by sorry
