-- Prove2me | Theorems.Thm_Formalism_REAL_weighted_square_integrable_filtration
-- name    : Formalism.REAL.weighted_square_integrable_filtration
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:14:53.718458+00:00
-- url     : https://prove2.me/theorems/01ff4a53-8acc-4e62-8afb-0e625320a234
-- title:
--   REAL: weighted square integrable filtration
-- statement:
--   The REAL construction uses the weighted square integrable filtration property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IntegrableComplexContinuousBoundedSupport.lean#L1458-L1495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IntegrableComplexContinuousBoundedSupport.lean#L1458-L1495

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

theorem Formalism.REAL.weighted_square_integrable_filtration (hl : HhLip) (hz : IntRdZero) {W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)}
    {c : ℂ} {a : ℝ} (ha : 0 ≤ a) (hsm : ∀ w ∈ W, SmoothOnG ε w)
    (hstab : ∀ w ∈ W, ∀ i j : Fin n, ε i = ε j → ∃ w' ∈ W, ∀ g, inUJ ε g → Eab ε i j w g = w' g)
    (hcas : ∀ w ∈ W, ∀ g, inUJ ε g → CasF ε w g = c * w g)
    (hint : ∀ w ∈ W, Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖w (toM g)‖ ^ 2)
      (muG ε)) :
    ∀ k : ℕ, ∀ w : List (Fin n × Fin n), w.length ≤ k → ∀ f ∈ W,
      Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eword ε w f (toM g)‖ ^ 2)
        (muG ε) := by sorry
