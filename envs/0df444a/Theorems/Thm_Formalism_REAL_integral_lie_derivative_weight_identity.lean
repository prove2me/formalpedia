-- Prove2me | Theorems.Thm_Formalism_REAL_integral_lie_derivative_weight_identity
-- name    : Formalism.REAL.integral_lie_derivative_weight_identity
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:13:59.00692+00:00
-- url     : https://prove2.me/theorems/3fa80476-1da3-4181-8ee9-638d5df71a29
-- title:
--   REAL: integral lie derivative weight identity
-- statement:
--   The REAL construction uses the integral lie derivative weight identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IntegrableComplexContinuousBoundedSupport.lean#L579-L625
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IntegrableComplexContinuousBoundedSupport.lean#L579-L625

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

theorem Formalism.REAL.integral_lie_derivative_weight_identity (hl : HhLip) (hz : IntRdZero) (a : ℝ) {R : ℝ} (hR : 0 < R)
    {u : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u) (i j : Fin n) :
    ∫ g : UJ ε, radialWeight a R (toM g) * Eab ε i j u (toM g) * starRingEnd ℂ (Eab ε i j u (toM g))
        ∂(muG ε) =
      -∫ g : UJ ε, Eab ε i j (radialWeight a R) (toM g) * u (toM g) * starRingEnd ℂ (Eab ε i j u (toM g))
        ∂(muG ε) +
      ((sgn ε i j : ℝ) : ℂ) * ∫ g : UJ ε, radialWeight a R (toM g) * u (toM g) *
        starRingEnd ℂ (Eab ε j i (Eab ε i j u) (toM g)) ∂(muG ε) := by sorry
