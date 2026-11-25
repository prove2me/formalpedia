-- Prove2me | Theorems.Thm_Formalism_REAL_norm_entry_mul_near_one_le
-- name    : Formalism.REAL.norm_entry_mul_near_one_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:51:39.367796+00:00
-- url     : https://prove2.me/theorems/16f3905d-f04a-5781-995f-72c1a81372a4
-- title:
--   REAL: norm entry mul near one le
-- statement:
--   The REAL construction uses the norm entry mul near one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L139-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L139-L153

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

theorem Formalism.REAL.norm_entry_mul_near_one_le {n : ℕ} {g u : Matrix (Fin n) (Fin n) ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hg : hs g ≤ R ^ 2) (hu : hs (u - 1) < 1 / 4) (i j : Fin n) :
    ‖(g * u) i j‖ ≤ R * (Real.sqrt n + 1) := by sorry
