-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_liftMatrix_conjTranspose
-- name    : Formalism.FourierDecayAlt.P.Wd11.liftMatrix_conjTranspose
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:47:59.369647+00:00
-- url     : https://prove2.me/theorems/4a5d514b-9a18-4cf7-a2b0-c00a8a07858f
-- title:
--   Wd11: lift Matrix conj Transpose
-- statement:
--   The Wd11 construction uses the lift Matrix conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L98-L102

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

theorem Formalism.FourierDecayAlt.P.Wd11.liftMatrix_conjTranspose [StarRing A] (M : M2 A) :
    (lift0 Mᴴ : M2 (SlopeTestRemainingChoices S A)) = (lift0 M)ᴴ := by sorry
