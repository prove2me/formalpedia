-- Prove2me | Theorems.Thm_Formalism_REAL_determinant_character_mul
-- name    : Formalism.REAL.determinant_character_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:23:16.511674+00:00
-- url     : https://prove2.me/theorems/69ae97be-056a-476a-bf2b-90164cc2e37c
-- title:
--   REAL: determinant character mul
-- statement:
--   The REAL construction uses the determinant character mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L98-L99

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

theorem Formalism.REAL.determinant_character_mul {n : ℕ} {ε : Fin n → Bool} (g h : UJ ε) :
    coeMatrixAlt ε (g * h) = coeMatrixAlt ε g * coeMatrixAlt ε h := by sorry
