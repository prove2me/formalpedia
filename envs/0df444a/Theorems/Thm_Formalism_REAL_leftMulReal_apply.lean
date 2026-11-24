-- Prove2me | Theorems.Thm_Formalism_REAL_leftMulReal_apply
-- name    : Formalism.REAL.leftMulReal_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:22:33.996272+00:00
-- url     : https://prove2.me/theorems/b82c666f-a6fb-49d4-a951-4811d899afea
-- title:
--   REAL: left Mul Real apply
-- statement:
--   The REAL construction uses the left Mul Real apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L63-L64

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

theorem Formalism.REAL.leftMulReal_apply {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (x : MatrixCoordinates n) :
    leftMulReal g x = Matrix.of.symm (g * Matrix.of x) := by sorry
