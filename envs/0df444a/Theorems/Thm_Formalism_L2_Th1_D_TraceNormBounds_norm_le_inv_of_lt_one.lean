-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_norm_le_inv_of_lt_one
-- name    : Formalism.L2.Th1.D.TraceNormBounds.norm_le_inv_of_lt_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:45:41.441568+00:00
-- url     : https://prove2.me/theorems/ecb2be5b-4227-440b-8d62-a14075be4ab3
-- title:
--   Trace Norm Bounds: norm le inv of lt one
-- statement:
--   The Trace Norm Bounds construction uses the norm le inv of lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/NormLeInvOfLtOne.lean#L105-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/NormLeInvOfLtOne.lean#L105-L125

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
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

theorem Formalism.L2.Th1.D.TraceNormBounds.norm_le_inv_of_lt_one {l : ℕ} (hl : 1 < l)
    (hval : ∀ a : K, a ≠ 0 → ∃ k : ℤ, ‖a‖ = (l : ℝ) ^ k) {y : K} (hy : ‖y‖ < 1) :
    ‖y‖ ≤ (l : ℝ)⁻¹ := by sorry
