-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_diagScalar_conjTranspose
-- name    : Formalism.FourierDecayAlt.P.Wd4.diagScalar_conjTranspose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:29.253843+00:00
-- url     : https://prove2.me/theorems/1605bb4b-335d-45bf-92ed-815a11f7d6c9
-- title:
--   Wd4: diag Scalar conj Transpose
-- statement:
--   The Wd4 construction uses the diag Scalar conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L383-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L383-L386

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

theorem Formalism.FourierDecayAlt.P.Wd4.diagScalar_conjTranspose (b : SlopeTestRemainingChoices S A) : (d0 b)ᴴ = d0 (star b) := by sorry
