-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_sim_ps
-- name    : Formalism.L2.Th1.D.TraceNormBounds.sim_ps
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:59:17.436641+00:00
-- url     : https://prove2.me/theorems/a68a11ff-8279-4d01-941e-68f2bb8e70f8
-- title:
--   Trace Norm Bounds: sim ps
-- statement:
--   The Trace Norm Bounds construction uses the sim ps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/CoboundaryCommutesHomomorphism.lean#L299-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/CoboundaryCommutesHomomorphism.lean#L299-L301

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

theorem Formalism.L2.Th1.D.TraceNormBounds.sim_ps {τ : Type} {g : MvPowerSeries τ K} (hg0 : constantCoeff g = 0) (hg : Integral g)
    {lam : PowerSeries K} (h : Simeq (lam : MvPowerSeries Unit K) 0) :
    Simeq (PowerSeries.subst g lam) 0 := by sorry
