-- Prove2me | Theorems.Thm_Formalism_REAL_sqrt_frobenius_add_le
-- name    : Formalism.REAL.sqrt_frobenius_add_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:52:07.146868+00:00
-- url     : https://prove2.me/theorems/5e8ccec8-918e-47a7-a303-f323009a38ee
-- title:
--   REAL: sqrt frobenius add le
-- statement:
--   The REAL construction uses the sqrt frobenius add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L88-L90

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
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

theorem Formalism.REAL.sqrt_frobenius_add_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Real.sqrt (hs (A + B)) ≤ Real.sqrt (hs A) + Real.sqrt (hs B) := by sorry
