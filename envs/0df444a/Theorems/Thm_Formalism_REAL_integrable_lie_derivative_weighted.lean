-- Prove2me | Theorems.Thm_Formalism_REAL_integrable_lie_derivative_weighted
-- name    : Formalism.REAL.integrable_lie_derivative_weighted
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:13:56.200967+00:00
-- url     : https://prove2.me/theorems/1493e501-31ea-45ea-aca6-1e07bb4b5503
-- title:
--   REAL: integrable lie derivative weighted
-- statement:
--   The REAL construction uses the integrable lie derivative weighted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IntegrableComplexContinuousBoundedSupport.lean#L849-L896
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IntegrableComplexContinuousBoundedSupport.lean#L849-L896

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

theorem Formalism.REAL.integrable_lie_derivative_weighted (hl : HhLip) (hz : IntRdZero) {a : ℝ} (ha : 0 ≤ a)
    {u : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u)
    (hu2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) (muG ε))
    (hT2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2)
      (muG ε)) (i j : Fin n) :
    Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2)
      (muG ε) := by sorry
