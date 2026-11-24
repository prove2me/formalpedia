-- Prove2me | Theorems.Thm_Formalism_REAL_right_derivative_real_comp
-- name    : Formalism.REAL.right_derivative_real_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:14:52.058595+00:00
-- url     : https://prove2.me/theorems/e3839149-1725-4a69-8021-51b58ecc969e
-- title:
--   REAL: right derivative real comp
-- statement:
--   The REAL construction uses the right derivative real comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IntegrableComplexContinuousBoundedSupport.lean#L138-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IntegrableComplexContinuousBoundedSupport.lean#L138-L154

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

theorem Formalism.REAL.right_derivative_real_comp {h : Matrix (Fin n) (Fin n) ℂ → ℝ} (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hh : SmoothOnG ε (fun x => ((h x : ℝ) : ℂ))) {g X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (hg : inUJ ε g) :
    Rd X (fun x => ((ψ (h x) : ℝ) : ℂ)) g =
      ((deriv ψ (h g) * (Rd X (fun x => ((h x : ℝ) : ℂ)) g).re : ℝ) : ℂ) := by sorry
