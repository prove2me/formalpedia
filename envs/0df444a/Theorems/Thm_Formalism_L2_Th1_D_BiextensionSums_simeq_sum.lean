-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_BiextensionSums_simeq_sum
-- name    : Formalism.L2.Th1.D.BiextensionSums.simeq_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:37:11.985723+00:00
-- url     : https://prove2.me/theorems/07d2c5be-3e4d-43b1-acc3-7f1070d6a5e7
-- title:
--   Biextension Sums: simeq sum
-- statement:
--   The Biextension Sums construction uses the simeq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionPointsOfExpSpec.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionPointsOfExpSpec.lean#L19-L28

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Pair
open Formalism.L2.Th1.D.BiextensionSums

theorem Formalism.L2.Th1.D.BiextensionSums.simeq_sum {K ι α : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
    (s : Finset α) (f g : α → MvPowerSeries ι K) (h : ∀ a ∈ s, Simeq (f a) (g a)) :
    Simeq (∑ a ∈ s, f a) (∑ a ∈ s, g a) := by sorry
