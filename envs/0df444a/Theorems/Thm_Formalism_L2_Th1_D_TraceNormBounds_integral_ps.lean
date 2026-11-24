-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_integral_ps
-- name    : Formalism.L2.Th1.D.TraceNormBounds.integral_ps
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:57:53.335799+00:00
-- url     : https://prove2.me/theorems/de30ee33-c015-4b54-b143-6877c540b833
-- title:
--   Trace Norm Bounds: integral ps
-- statement:
--   The Trace Norm Bounds construction uses the integral ps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/CoboundaryCommutesHomomorphism.lean#L274-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/CoboundaryCommutesHomomorphism.lean#L274-L278

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open MvPowerSeries
open Formalism.L2.Th1.D.TraceNormBounds
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem Formalism.L2.Th1.D.TraceNormBounds.integral_ps {τ : Type} {g : MvPowerSeries τ K} (hg0 : constantCoeff g = 0)
    (hg : Integral g) {θ : PowerSeries K} (h : ∀ n, ‖PowerSeries.coeff n θ‖ ≤ 1) :
    Integral (PowerSeries.subst g θ) := by sorry
