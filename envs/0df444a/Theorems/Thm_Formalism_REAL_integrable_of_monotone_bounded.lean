-- Prove2me | Theorems.Thm_Formalism_REAL_integrable_of_monotone_bounded
-- name    : Formalism.REAL.integrable_of_monotone_bounded
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:13:20.107799+00:00
-- url     : https://prove2.me/theorems/34e51b89-e45b-4d98-b0f0-ed2fba99360b
-- title:
--   REAL: integrable of monotone bounded
-- statement:
--   The REAL construction uses the integrable of monotone bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IntegrableComplexContinuousBoundedSupport.lean#L815-L831
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IntegrableComplexContinuousBoundedSupport.lean#L815-L831

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasComm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IntegrableComplexContinuousBoundedSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ENNReal
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}

theorem Formalism.REAL.integrable_of_monotone_bounded {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : ℕ → X → ℝ} {f : X → ℝ}
    (hF : ∀ N, Integrable (F N) μ) (hF0 : ∀ N x, 0 ≤ F N x) (hmono : ∀ x, Monotone (fun N => F N x))
    (hlim : ∀ x, ∃ N, F N x = f x) (hle : ∀ N x, F N x ≤ f x) (hf : AEStronglyMeasurable f μ)
    {B : ℝ} (hB : ∀ N, ∫ x, F N x ∂μ ≤ B) : Integrable f μ := by sorry
