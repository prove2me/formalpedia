-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_B4_subst_C_mul_sum
-- name    : Formalism.L2.Th1.D.B4.subst_C_mul_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:25:48.527447+00:00
-- url     : https://prove2.me/theorems/e9b8ae72-2caf-4694-a1fa-f17e7e7acfbc
-- title:
--   B4: subst C mul sum
-- statement:
--   The B4 construction uses the subst C mul sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionHypothesesOfConditions.lean#L210-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionHypothesesOfConditions.lean#L210-L214

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp NoLowBidegree letterLog de1 de2 s0 s1 s2 s1' s2' V2 degE)
open Formalism.InvariantFactorPaths.G7 (Simeq DivAB UnrOK IsLawOfLog)
open MvPowerSeries (subst HasSubst constantCoeff)
open B4
open Formalism.L2.Th1.D.B4
variable {K : Type} [Field K] {τ τ' : Type}

theorem Formalism.L2.Th1.D.B4.subst_C_mul_sum {a : τ → MvPowerSeries τ' K} (ha : HasSubst a) (c : K) {α : Type}
    (s : Finset α) (f : α → MvPowerSeries τ K) :
    subst a (MvPowerSeries.C c * ∑ k ∈ s, f k) = MvPowerSeries.C c * ∑ k ∈ s, subst a (f k) := by sorry
