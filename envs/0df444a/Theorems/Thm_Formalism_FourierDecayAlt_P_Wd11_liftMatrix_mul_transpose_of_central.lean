-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_liftMatrix_mul_transpose_of_central
-- name    : Formalism.FourierDecayAlt.P.Wd11.liftMatrix_mul_transpose_of_central
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:01.842422+00:00
-- url     : https://prove2.me/theorems/8289ab9e-a3e3-43d1-89f5-8b3501e3f49a
-- title:
--   Wd11: lift Matrix mul transpose of central
-- statement:
--   The Wd11 construction uses the lift Matrix mul transpose of central property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L157-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L157-L161

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

theorem Formalism.FourierDecayAlt.P.Wd11.liftMatrix_mul_transpose_of_central {N : M2 A} (hN : Cen N) (M : M2 (SlopeTestRemainingChoices S A)) :
    (lift0 N * M)ᵀ = Mᵀ * lift0 Nᵀ := by sorry
