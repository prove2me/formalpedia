-- Prove2me | Theorems.Thm_Formalism_REAL_of_leftMulReal_apply
-- name    : Formalism.REAL.of_leftMulReal_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:52:03.341017+00:00
-- url     : https://prove2.me/theorems/99f11ed2-8f68-4859-9e8b-009bb5f65e32
-- title:
--   REAL: of left Mul Real apply
-- statement:
--   The REAL construction uses the of left Mul Real apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L94-L96

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PlaceRankTwoOne
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Metric Kronecker
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.of_leftMulReal_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : MatrixCoordinates n) :
    Matrix.of (leftMulReal A x) = A * Matrix.of x := by sorry
