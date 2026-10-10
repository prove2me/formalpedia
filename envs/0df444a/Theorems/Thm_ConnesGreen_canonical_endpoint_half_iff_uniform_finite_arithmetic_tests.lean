-- Prove2me | Theorems.Thm_ConnesGreen_canonical_endpoint_half_iff_uniform_finite_arithmetic_tests
-- name    : ConnesGreen.canonical_endpoint_half_iff_uniform_finite_arithmetic_tests
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T02:12:51.638637+00:00
-- url     : https://prove2.me/theorems/38c4e70e-1332-4921-bf6a-cc48bffcda12
-- title:
--   Original ordered endpoint half-bound iff uniform finite-restored arithmetic tests
-- statement:
--   For every nonnegative endpoint $c$ and every finite selected packet $S$ of ACTUAL nontrivial zeta zeros, the original ordered support-right marker satisfies $\tfrac12 I\le G^+_{c,S}$ if and only if the following uniform arithmetic condition holds. For every $0<\eta<1/2$ there is a neighborhood size $\delta>0$ such that for every regularization $\varepsilon>0$ there is a finite reflection-closed restoration packet $F\supseteq S$ working for ALL positive windows $c<T<c+\delta$ and ALL original smooth tests supported strictly in that window. At each window, the complete negative covariance outside $F$ has norm at most $(\eta/2)\varepsilon$, the original restored denominator $A_F=C_T+\varepsilon I-D_{T,F}$ is strictly positive, and every such test obeys
--   $$
--   \|M_S^*x_g\|^2\le ((1/2-\eta)^{-1}-1)\left(\operatorname{Re}W(g*\operatorname{starInv}(g))+\|M_F^*x_g\|^2+\varepsilon E(g)\right).
--   $$
--   Here $x_g$ is the ORIGINAL embedded $Lg$, and $E(g)$ is exactly the integral of $|g'|^2$ plus one quarter of the integral of $|g|^2$. The selected packet remains $S$; $F$ is a distinct restoration cutoff. The neighborhood is chosen BEFORE regularization, and the restoration cutoff BEFORE the window and test. The full actual-zero complement, analytic multiplicities, reflected column normalization, physical carrier and unchanged signed Weil distribution are retained.
--
--   This is an exact criterion for an arbitrary nonnegative parameter $c$, including $c=0$ and empty selected packets. It does not establish the displayed arithmetic condition at the intended critical endpoint, identify that endpoint, or prove a neutral-shell bound or RH. Positive regularization tends to zero first; support tends to the endpoint from the right second. No limit or quantifier order is exchanged.
-- source:
--   Existing native Connes–Weil development, WeilDefect/Connes/CanonicalGreenQuadraticEndpoint.lean, theorem ConnesGreen.canonical_endpoint_half_iff_uniform_finite_arithmetic_tests; exact source SHA256 a8f1724cb60c29fc5c8c599f9bfb98ecb7ec0c466ddf171ff8c8d7ae62604e90. Recovered checkpoint Connes_Weil_RG0_Finite_Arithmetic_Tests.zip SHA256 be34a9178df35e6cb4fe9704b22cbdbdaed99beb0374b7dd4367e11658cdc553. Public signature unfolds only physicalTestEnergy; independent native signature and complete proof assembly checked. Separate RPB108 original-form attachments remain future work.

import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
import Definitions.Def_WeilMarker_regularized_cost
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_endpoint_half_iff_uniform_finite_arithmetic_tests
    (c : ℝ) (hc : 0 ≤ c) (S : Finset CriticalZeros) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S ↔
    ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ∃ F : Finset CriticalZeros, S ⊆ F ∧
        (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
        ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + δ →
          ‖canonicalTailCovariance T hT F‖ ≤ (η / 2) * ε ∧
          IsStrictlyPositive (canonicalPositiveCovariance T hT + ε • 1 -
            canonicalTailCovariance T hT F) ∧
          ∀ g : ℝ → ℂ, SupportedTest T g →
            ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 ≤
            ((1 / 2 - η)⁻¹ - 1) * ((weilDistribution (conv g (starInv g))).re +
              ‖(canonicalSelectedSynthesis T hT F).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 +
              ε * ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) + (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))) := by sorry
