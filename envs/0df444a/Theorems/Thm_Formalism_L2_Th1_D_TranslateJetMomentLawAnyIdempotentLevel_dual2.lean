-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_dual2
-- name    : Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.dual2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:36:32.319557+00:00
-- url     : https://prove2.me/theorems/92dfc0e1-5a04-4bd4-b46b-9f97f1bca8c0
-- title:
--   Translate Jet Moment Law Any Idempotent Level: dual2
-- statement:
--   The Translate Jet Moment Law Any Idempotent Level construction uses the dual2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FirstMomentIdempotentLaw.lean#L124-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FirstMomentIdempotentLaw.lean#L124-L140

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
open Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
open Pair KernelCokernelKilling
variable {K : Type} [Field K] {d : ℕ} [NeZero d]
variable {ι : Type}

theorem Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.dual2 [Fintype ι] [DecidableEq ι] (hd : Even d) (σ : K →+* K) {om oms : ι → K}
    (hfix : ∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) (hT : TrDual d σ om oms)
    (s s' : ZMod d) :
    (∑ x : Bool × ι, mXY σ om oms s x * pXY σ om oms x s') = if s = s' then 1 else 0 := by sorry
