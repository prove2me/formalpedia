-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_freeOf2_mul
-- name    : Formalism.FourierDecayAlt.P.Wd10.freeOf2_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:49.374115+00:00
-- url     : https://prove2.me/theorems/282ce499-9fea-4d43-becf-2bed5c5669ce
-- title:
--   Wd10: free Of2 mul
-- statement:
--   The Wd10 construction uses the free Of2 mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PartialFlipCommuteDiagScalarOfFree.lean#L118-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PartialFlipCommuteDiagScalarOfFree.lean#L118-L123

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf2_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd10
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd10.freeOf2_mul {a : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) (hN : FreeOf2 a N) :
    FreeOf2 a (M * N) := by sorry
