-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_freeOf_diagScalar
-- name    : Formalism.FourierDecayAlt.P.Wd4.freeOf_diagScalar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:38.003666+00:00
-- url     : https://prove2.me/theorems/e6502f9f-05e4-4d0d-9a96-3e235dde3b08
-- title:
--   Wd4: free Of diag Scalar
-- statement:
--   The Wd4 construction uses the free Of diag Scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L365-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L365-L371

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
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd4.freeOf_diagScalar {a : S} {b : SlopeTestRemainingChoices S A} (hb : FreeOf a b) : FreeOf2 a (d0 b) := by sorry
