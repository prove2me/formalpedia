-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_sum_rule
-- name    : Formalism.L2.Th1.D.InverseCommuting.sum_rule
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:36:53.036656+00:00
-- url     : https://prove2.me/theorems/ddfc85b4-572b-42c5-b21e-d14a7b25ef0e
-- title:
--   Inverse Commuting: sum rule
-- statement:
--   The Inverse Commuting construction uses the sum rule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TilInvariantLOf.lean#L84-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TilInvariantLOf.lean#L84-L105

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TilInvariantLOf
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
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Formalism.L2.Th1.D.InverseCommuting
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {τ : Type}

theorem Formalism.L2.Th1.D.InverseCommuting.sum_rule {P : MvPowerSeries τ K → Prop} (h0 : P 0) (hadd : ∀ g g', P g → P g' → P (g + g'))
    (φ : MvPowerSeries τ K → MvPowerSeries τ K)
    (hφ : ∀ g g', P g → P g' → Simeq (φ (g + g')) (φ g + φ g'))
    {α : Type} (s : Finset α) (g : α → MvPowerSeries τ K) (hg : ∀ i ∈ s, P (g i)) :
    P (∑ i ∈ s, g i) ∧ Simeq (φ (∑ i ∈ s, g i)) (∑ i ∈ s, φ (g i)) := by sorry
