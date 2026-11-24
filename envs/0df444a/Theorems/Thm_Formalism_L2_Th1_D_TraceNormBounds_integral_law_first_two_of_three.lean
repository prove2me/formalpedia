-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_integral_law_first_two_of_three
-- name    : Formalism.L2.Th1.D.TraceNormBounds.integral_law_first_two_of_three
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:57:46.288402+00:00
-- url     : https://prove2.me/theorems/90075fab-7c1c-4d36-a845-94e4155b287c
-- title:
--   Trace Norm Bounds: integral law first two of three
-- statement:
--   The Trace Norm Bounds construction uses the integral law first two of three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/CoboundaryCommutesHomomorphism.lean#L317-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/CoboundaryCommutesHomomorphism.lean#L317-L320

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

theorem Formalism.L2.Th1.D.TraceNormBounds.integral_law_first_two_of_three {F : MvPowerSeries (Fin 2) K} (hF : Integral F) : Integral (in3 F) := by sorry
