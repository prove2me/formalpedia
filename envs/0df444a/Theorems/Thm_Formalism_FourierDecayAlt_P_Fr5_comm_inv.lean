-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_comm_inv
-- name    : Formalism.FourierDecayAlt.P.Fr5.comm_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:22.192823+00:00
-- url     : https://prove2.me/theorems/00ccbd3a-563c-4d9e-80db-c818ff4bf128
-- title:
--   Fr5: comm inv
-- statement:
--   The Fr5 construction uses the comm inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L13-L17

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {B : Type} [Ring B] [StarRing B] [Algebra ℂ B]

theorem Formalism.FourierDecayAlt.P.Fr5.comm_inv {x xi g : B} (h1 : x * xi = 1) (h2 : xi * x = 1) (h : Commute x g) : Commute xi g := by sorry
