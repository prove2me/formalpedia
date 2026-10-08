-- Prove2me | Theorems.Thm_ConnesGreen_canonical_uniform_marker_gap_of_supported_negative_test
-- name    : ConnesGreen.canonical_uniform_marker_gap_of_supported_negative_test
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T06:03:49.988482+00:00
-- url     : https://prove2.me/theorems/280c2f2d-1255-4e5c-9be1-27d81abb6079
-- title:
--   One original negative test gives a common regularized gap on every larger window
-- statement:
--   Given one original supported test $g$ on $t>0$ with negative original selected quadratic value for an unchanged finite actual-zero packet $S$, we prove existence of constants $\beta,\delta$, chosen before the larger window, with
--   $$0<\beta<\tfrac12,\quad\delta>0,\quad
--   \forall T\ge t\ \forall\,0<\varepsilon<\delta,\quad \beta I\not\le G_{S,\varepsilon}(T).$$
--   Here $G_{S,\varepsilon}(T)$ is the existing original regularized marker. Put $p=\|P_t^*x_t\|^2$, $b=\|M_{t,S}^*x_t\|^2$, and let $E$ be the original global Dirichlet energy of $g$. The negative-test hypothesis gives $p<b$. A closed scalar-margin lemma chooses $\kappa>1$ and $\delta>0$ so that
--   $$\kappa(p+\varepsilon E)<b\qquad(0<\varepsilon<\delta).$$
--   Set $\beta=(\kappa+1)^{-1}<1/2$. The same original test remains supported in every larger window. Accepted original analysis-norm independence keeps $p,b$ unchanged, and accepted actual_physical_test_norm identifies its source norm squared with the same global $E$. The accepted negative_margin_forbids_marker_lower excludes the displayed marker lower bound. All original carriers, source embeddings, actors, actual zeros and reflected-pair normalization remain unchanged. Existence of the negative test is an explicit premise of this reduction, not a conclusion of it.
-- source:
--   monocap-tech/weil at 85e4b8c3ed3f67e549834b0640d490c1f6537295; WeilDefect/Connes/SupportedNegativeUniformGap.lean (new additive module), retaining original actor, carrier, marker and source definitions.

import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open WeilDefect.MarkerStability

theorem ConnesGreen.canonical_uniform_marker_gap_of_supported_negative_test (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g)
    (hn : ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 < 0):
    ∃ β δ : ℝ, 0 < β ∧ β < 1 / 2 ∧ 0 < δ ∧
      ∀ T : ℝ, ∀ hT : 0 < T, t ≤ T → ∀ ε : ℝ, 0 < ε → ε < δ →
        ¬ β • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalRegularizedMarker T hT S ε := by sorry
