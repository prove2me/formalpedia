-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_B4_simeq_sum
-- name    : Formalism.L2.Th1.D.B4.simeq_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:39:25.757414+00:00
-- url     : https://prove2.me/theorems/81388c3b-ab37-4da4-bd56-668047d360a0
-- title:
--   B4: simeq sum
-- statement:
--   The B4 construction uses the simeq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionHypothesesOfConditions.lean#L109-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionHypothesesOfConditions.lean#L109-L117

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_simeq_sum

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
open Formalism.L2.Th1.D.B4
variable {K ι : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem Formalism.L2.Th1.D.B4.simeq_sum {α : Type} (s : Finset α) (f g : α → MvPowerSeries ι K)
    (h : ∀ a ∈ s, Simeq (f a) (g a)) : Simeq (∑ a ∈ s, f a) (∑ a ∈ s, g a) := by sorry
