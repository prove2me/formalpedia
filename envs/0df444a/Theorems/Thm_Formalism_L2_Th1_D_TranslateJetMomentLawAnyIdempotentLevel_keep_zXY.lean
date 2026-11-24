-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_keep_zXY
-- name    : Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.keep_zXY
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:24.580102+00:00
-- url     : https://prove2.me/theorems/c687d1e5-8b7d-4a61-a0bf-ca8d587440fb
-- title:
--   Translate Jet Moment Law Any Idempotent Level: keep z XY
-- statement:
--   The Translate Jet Moment Law Any Idempotent Level construction uses the keep z XY property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FirstMomentIdempotentLaw.lean#L373-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FirstMomentIdempotentLaw.lean#L373-L408

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog frobVar frobVar_eq_expand)
open MvPowerSeries
open Pair TranslateJetMomentLawAnyIdempotentLevel
open Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
open Pair KernelCokernelKilling
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.keep_zXY {l d : ℕ} [NeZero d] {ι : Type} [Fintype ι] (σ : K →+* K) (om oms : ι → K)
    (j : ZMod d) :
    keep (fun x : Bool × ι => (x.1 = false ↔ j.val % 2 = 0)) (zXY l σ om oms j) =
      zXY l σ om oms j := by sorry
