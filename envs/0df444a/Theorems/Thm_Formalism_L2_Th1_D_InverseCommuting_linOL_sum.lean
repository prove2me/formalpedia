-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_linOL_sum
-- name    : Formalism.L2.Th1.D.InverseCommuting.linOL_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:36:25.625846+00:00
-- url     : https://prove2.me/theorems/fb263d66-592d-4b39-9abd-eea0011479ba
-- title:
--   Inverse Commuting: lin OL sum
-- statement:
--   The Inverse Commuting construction uses the lin OL sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TilInvariantLOf.lean#L129-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TilInvariantLOf.lean#L129-L143

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
variable {K : Type} [NormedField K] {τ : Type} {d : ℕ} [NeZero d]

theorem Formalism.L2.Th1.D.InverseCommuting.linOL_sum (σ : K →+* K) {ι : Type} [Fintype ι] (a y : ι → K)
    (ha : ∀ i, σ (σ (a i)) = a i) (L : ZMod d → MvPowerSeries τ K) :
    linOL σ (∑ i, a i * y i) L = ∑ i, C (σ (a i)) * linOL σ (y i) L := by sorry
