-- Prove2me | Theorems.Thm_Formalism_REAL_det_leftMul_restrictScalars
-- name    : Formalism.REAL.det_leftMul_restrictScalars
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:23:44.824143+00:00
-- url     : https://prove2.me/theorems/71884def-ec34-4557-873e-b9a89dd884b8
-- title:
--   REAL: det left Mul restrict Scalars
-- statement:
--   The REAL construction uses the det left Mul restrict Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L32-L34

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

theorem Formalism.REAL.det_leftMul_restrictScalars {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det ((LinearMap.mulLeft ℂ g).restrictScalars ℝ) = Complex.normSq g.det ^ n := by sorry
