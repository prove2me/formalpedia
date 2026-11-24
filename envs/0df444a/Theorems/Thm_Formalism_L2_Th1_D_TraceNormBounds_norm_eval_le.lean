-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_norm_eval_le
-- name    : Formalism.L2.Th1.D.TraceNormBounds.norm_eval_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:58:40.120622+00:00
-- url     : https://prove2.me/theorems/1af6d984-54cf-4a8d-9941-c9b8b5a0bf2d
-- title:
--   Trace Norm Bounds: norm eval le
-- statement:
--   The Trace Norm Bounds construction uses the norm eval le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/NormLeInvOfLtOne.lean#L86-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/NormLeInvOfLtOne.lean#L86-L103

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Theorems.Thm_Formalism_LT_TorsProof_norm_eval_le

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
open Formalism.L2.Th1.D.TraceNormBounds
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem Formalism.L2.Th1.D.TraceNormBounds.norm_eval_le (Q : Polynomial ℤ) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖Polynomial.eval₂ (Int.castRingHom K) x Q‖ ≤ 1 := by sorry
