-- Prove2me | Theorems.Thm_Formalism_REAL_integrable_lie_derivative_pairing
-- name    : Formalism.REAL.integrable_lie_derivative_pairing
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:13:42.55619+00:00
-- url     : https://prove2.me/theorems/897ac7dd-7c55-43a5-bf36-8f3be5d48d98
-- title:
--   REAL: integrable lie derivative pairing
-- statement:
--   The REAL construction uses the integrable lie derivative pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IntegrableComplexContinuousBoundedSupport.lean#L956-L1065
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IntegrableComplexContinuousBoundedSupport.lean#L956-L1065

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

theorem Formalism.REAL.integrable_lie_derivative_pairing (hl : HhLip) (hz : IntRdZero) {a : ℝ} (ha : 0 ≤ a)
    {u u' : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u) (hu' : SmoothOnG ε u')
    (hu2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) (muG ε))
    (hu2' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u' (toM g)‖ ^ 2) (muG ε))
    (i j : Fin n)
    (hv2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2)
      (muG ε))
    (hv2' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eab ε j i u' (toM g)‖ ^ 2)
      (muG ε)) :
    ∫ g : UJ ε, Eab ε i j u (toM g) * starRingEnd ℂ (u' (toM g)) ∂(muG ε) =
      ((sgn ε i j : ℝ) : ℂ) * ∫ g : UJ ε, u (toM g) * starRingEnd ℂ (Eab ε j i u' (toM g)) ∂(muG ε) := by sorry
