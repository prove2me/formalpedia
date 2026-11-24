-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_law_right_zero
-- name    : Formalism.L2.Th1.D.TraceNormBounds.law_right_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:01:15.711734+00:00
-- url     : https://prove2.me/theorems/7a2a91fb-43a2-4ff9-874a-5738a4f3ac2a
-- title:
--   Trace Norm Bounds: law right zero
-- statement:
--   The Trace Norm Bounds construction uses the law right zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/CoboundaryCommutesHomomorphism.lean#L205-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/CoboundaryCommutesHomomorphism.lean#L205-L215

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
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.D.TraceNormBounds.law_right_zero {l : ℕ} (hl : 2 ≤ l) {F : MvPowerSeries (Fin 2) K}
    (hF0 : constantCoeff F = 0) (hF : cob F (lgF K l) = 0) {τ : Type} {a : MvPowerSeries τ K}
    (ha : constantCoeff a = 0) : subst ![a, 0] F = a := by sorry
