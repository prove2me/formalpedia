-- Prove2me | Theorems.Thm_Formalism_REAL_stdBasis_repr_apply
-- name    : Formalism.REAL.stdBasis_repr_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:22:50.766909+00:00
-- url     : https://prove2.me/theorems/4b2ee46e-2a92-4560-b969-2f48607cef5c
-- title:
--   REAL: std Basis repr apply
-- statement:
--   The REAL construction uses the std Basis repr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean#L12-L14

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

theorem Formalism.REAL.stdBasis_repr_apply (n : ℕ) (x : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (Matrix.stdBasis ℂ (Fin n) (Fin n)).repr x (i, j) = x i j := by sorry
