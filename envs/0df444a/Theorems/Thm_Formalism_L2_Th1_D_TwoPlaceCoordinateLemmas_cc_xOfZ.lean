-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TwoPlaceCoordinateLemmas_cc_xOfZ
-- name    : Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas.cc_xOfZ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:29:35.977672+00:00
-- url     : https://prove2.me/theorems/78a273d1-3206-5c86-8936-2854e327e2fd
-- title:
--   Two Place Coordinate Lemmas: cc x Of Z
-- statement:
--   The Two Place Coordinate Lemmas construction uses the cc x Of Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TwoPlaces.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TwoPlaces.lean#L16-L22

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

theorem Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas.cc_xOfZ {K0 K : Type} [Field K0] [Field K] {ι : Type} {d N0 N1 : ℕ} [NeZero d] {l : ℕ}
    (hl : 2 ≤ l) (j : K0 →+* K) (σ : K0 →+* K0) (om oms : ι → K0) (x : PV ι N0 N1) :
    constantCoeff (xOfZ (d := d) l j σ om oms x) = 0 := by sorry
