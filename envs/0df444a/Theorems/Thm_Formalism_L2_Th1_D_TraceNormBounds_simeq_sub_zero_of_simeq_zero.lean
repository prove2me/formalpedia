-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_simeq_sub_zero_of_simeq_zero
-- name    : Formalism.L2.Th1.D.TraceNormBounds.simeq_sub_zero_of_simeq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:58:33.893842+00:00
-- url     : https://prove2.me/theorems/d5fdb444-c73d-4673-ae44-36f237536219
-- title:
--   Trace Norm Bounds: simeq sub zero of simeq zero
-- statement:
--   The Trace Norm Bounds construction uses the simeq sub zero of simeq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/CoboundaryCommutesHomomorphism.lean#L303-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/CoboundaryCommutesHomomorphism.lean#L303-L309

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

theorem Formalism.L2.Th1.D.TraceNormBounds.simeq_sub_zero_of_simeq_zero {τ : Type} {f g : MvPowerSeries τ K} (hf : Simeq f 0) (hg : Simeq g 0) :
    Simeq (f - g) 0 := by sorry
