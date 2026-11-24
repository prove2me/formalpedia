-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_funEq_of_shift
-- name    : Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.funEq_of_shift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:35:18.066257+00:00
-- url     : https://prove2.me/theorems/07fea0cf-77cc-4838-aa8e-1c0a8f076745
-- title:
--   Translate Jet Moment Law Any Idempotent Level: fun Eq of shift
-- statement:
--   The Translate Jet Moment Law Any Idempotent Level construction uses the fun Eq of shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FirstMomentIdempotentLaw.lean#L493-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FirstMomentIdempotentLaw.lean#L493-L503

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
variable {K : Type} [NormedField K] {d : ℕ} [NeZero d] {ι : Type}

theorem Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.funEq_of_shift {l : ℕ} (hq : l ^ 2 ≠ 0) (σ : K →+* K) {τ : Type}
    {L : ZMod d → MvPowerSeries τ K} (hL : ShiftType l σ L) :
    Formalism.FG.IsFunEqTypeV l (l ^ 2) hq (σ.comp σ) (sM K d) L := by sorry
