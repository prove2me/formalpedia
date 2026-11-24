-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_mul_lift0_transpose
-- name    : Formalism.FourierDecayAlt.P.Wd11.mul_lift0_transpose
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:06.473143+00:00
-- url     : https://prove2.me/theorems/4c71ed08-f976-4b09-90a2-9ac06d90b0d2
-- title:
--   Wd11: mul lift0 transpose
-- statement:
--   The Wd11 construction uses the mul lift0 transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L163-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L163-L167

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

theorem Formalism.FourierDecayAlt.P.Wd11.mul_lift0_transpose {N : M2 A} (hN : Cen N) (M : M2 (SlopeTestRemainingChoices S A)) :
    (M * lift0 N)ᵀ = lift0 Nᵀ * Mᵀ := by sorry
