-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TwoPlaceCoordinateLemmas_two
-- name    : Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas.two
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:03:01.582512+00:00
-- url     : https://prove2.me/theorems/c2de33d9-902a-5826-9c08-4e1efe26f4f5
-- title:
--   Two Place Coordinate Lemmas: two
-- statement:
--   The Two Place Coordinate Lemmas construction uses the two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TwoPlaces.lean#L169-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TwoPlaces.lean#L169-L169

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_TwoPlaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_SecondLevelOfNorm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionRelationOfExpSpec
import Definitions.Def_Formalism_GaussJetBounds_StatementW
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TwoPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog bSum idM ZV serAlong HasJetBound OrbitsMul opAlong jetPairPoly)
open Formalism.InvariantFactorPaths.G7 (Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Formalism.L2.Th1.D Formalism.L2.Th1.D.BiextensionAlongSeries

theorem Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas.two : TwoPlaces := by sorry
