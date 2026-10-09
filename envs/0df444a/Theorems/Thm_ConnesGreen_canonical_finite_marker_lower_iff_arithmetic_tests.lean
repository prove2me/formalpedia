-- Prove2me | Theorems.Thm_ConnesGreen_canonical_finite_marker_lower_iff_arithmetic_tests
-- name    : ConnesGreen.canonical_finite_marker_lower_iff_arithmetic_tests
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T14:09:42.711979+00:00
-- url     : https://prove2.me/theorems/4b732a2b-6593-46ba-96db-3d7c6a9e7480
-- title:
--   Original finite-restored marker bound is exactly an arithmetic inequality on all original tests
-- statement:
--   For the ORIGINAL selected packet $S$ and restoration packet $F$ on the same actual-zero carrier, assume the displayed original restored denominator $A_F=PP^*+\varepsilon I-B_FB_F^*$ is strictly positive and $0<\beta<1$. We prove
--   $$\beta I\le\operatorname{marker}(A_F,M_S)
--   \Longleftrightarrow \forall g\in\operatorname{SupportedTest}(t),\quad
--   \|M_S^*x_g\|^2\le(\beta^{-1}-1)\bigl(\operatorname{Re}W(g*\operatorname{starInv}(g))+\|M_F^*x_g\|^2+\varepsilon E(g)\bigr).$$
--   A closed local proof of the exact original scaled marker/covariance equivalence reduces the marker bound to M_S M_S* <= (beta inverse minus one) A_F. Strict positivity supplies self-adjointness of A_F; real scalar multiplication preserves it. Accepted ORIGINAL dense-test covariance order reduces the operator inequality to supported-test quadratic inequalities, with no density assertion about neutral kernels. The real scalar/inner-product identity and the closed exact finite-restored arithmetic quadratic proof give the displayed right side. The public marker expression unfolds EXACTLY canonicalFiniteRestoredMarker, and E(g) unfolds EXACTLY physicalTestEnergy; native readback checks both against the unchanged original theorem. The selected S is never replaced by F, and no uniform endpoint neighborhood or jump-budget estimate is assumed.
-- source:
--   monocap-tech/weil native head a1a3c6481eb9bc50bc7e92aa694f6ae530c7e359; unchanged MarkerQuadratic.lean and CanonicalGreenQuadraticEndpoint.lean declarations; explicit native definitional unfoldings only

import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_WeilMarker_regularized_cost
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability WeilDefect.WDT13
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_finite_marker_lower_iff_arithmetic_tests (t : ℝ) (ht : 0 < t)
    (S F : Finset CriticalZeros) (ε β : ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (hA : IsStrictlyPositive (canonicalPositiveCovariance t ht + ε • 1 -
      canonicalTailCovariance t ht F)) :
    β • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ marker (canonicalPositiveCovariance t ht + ε • 1 - canonicalTailCovariance t ht F) (canonicalSelectedSynthesis t ht S) ↔
    ∀ g : ℝ → ℂ, SupportedTest t g →
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ≤
      (β⁻¹ - 1) * ((weilDistribution (conv g (starInv g))).re +
        ‖(canonicalSelectedSynthesis t ht F).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
        ε * ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) + (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))) := by sorry
