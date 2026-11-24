-- Prove2me | Theorems.Thm_Formalism_REAL_norm_sub_one_lt_half
-- name    : Formalism.REAL.norm_sub_one_lt_half
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:22:51.740015+00:00
-- url     : https://prove2.me/theorems/6071d8fd-a52f-494d-b507-89b126d60a3a
-- title:
--   REAL: norm sub one lt half
-- statement:
--   The REAL construction uses the norm sub one lt half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L111-L114

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

theorem Formalism.REAL.norm_sub_one_lt_half {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : hs (u - 1) < 1 / 4) :
    ‖u - 1‖ < 1 / 2 := by sorry
