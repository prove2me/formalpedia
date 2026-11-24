-- Prove2me | Theorems.Thm_Formalism_REAL_integrable_mul_conj_of_weighted
-- name    : Formalism.REAL.integrable_mul_conj_of_weighted
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:14:16.858801+00:00
-- url     : https://prove2.me/theorems/fed0c987-ad5c-40a4-a982-f62413053a5d
-- title:
--   REAL: integrable mul conj of weighted
-- statement:
--   The REAL construction uses the integrable mul conj of weighted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IntegrableComplexContinuousBoundedSupport.lean#L903-L923
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IntegrableComplexContinuousBoundedSupport.lean#L903-L923

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

theorem Formalism.REAL.integrable_mul_conj_of_weighted {a : ℝ} (ha : 0 ≤ a) {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f')
    (h2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f (toM g)‖ ^ 2) (muG ε))
    (h2' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f' (toM g)‖ ^ 2) (muG ε)) :
    Integrable (fun g : UJ ε => f (toM g) * starRingEnd ℂ (f' (toM g))) (muG ε) := by sorry
