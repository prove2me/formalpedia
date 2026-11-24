-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_sandwich_transpose
-- name    : Formalism.FourierDecayAlt.P.Wd11.diagScalar_sandwich_transpose
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:47:50.783952+00:00
-- url     : https://prove2.me/theorems/4090ebbc-9a38-4915-8ec5-0a7fc95f9f11
-- title:
--   Wd11: diag Scalar sandwich transpose
-- statement:
--   The Wd11 construction uses the diag Scalar sandwich transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L151-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L151-L155

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd11.diagScalar_sandwich_transpose (x y : SlopeTestRemainingChoices S A) (M : M2 (SlopeTestRemainingChoices S A)) :
    (d0 x * M * d0 y)ᵀ = d0 x * Mᵀ * d0 y := by sorry
