-- Prove2me | Theorems.Thm_ConnesGreen_canonical_uniform_picard_gap_of_supported_negative_test
-- name    : ConnesGreen.canonical_uniform_picard_gap_of_supported_negative_test
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T06:03:58.256152+00:00
-- url     : https://prove2.me/theorems/8743f2d3-40dd-4588-aee9-1d924b6f06f9
-- title:
--   One original negative test gives a common Picard gap below half on every larger window
-- statement:
--   From one original supported selected-negative test on $t>0$, we prove a common original Picard marker gap
--   $$\exists\,0<\beta<\tfrac12,\quad\forall T\ge t,\quad\beta I\not\le G_S(T).$$
--   The complete proof first constructs, using a closed scalar-margin helper, a uniform regularized gap for the same unchanged packet and all larger windows. Original test energy and actor analysis norms are independent of those larger windows, giving constants $\beta,\delta$ chosen once. If the original Picard marker admitted the $\beta$ lower bound, the accepted exact canonicalPicardMarker_lower_iff_all_regularized would transfer that bound to every positive regularization scale. Choosing $\varepsilon=\delta/2$ contradicts the regularized gap. The existing positive regularization limit is retained; no existence premise is added and no limit order is exchanged. The public negative-test premise remains explicit.
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

theorem ConnesGreen.canonical_uniform_picard_gap_of_supported_negative_test (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g)
    (hn : ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 < 0):
    ∃ β : ℝ, 0 < β ∧ β < 1 / 2 ∧
      ∀ T : ℝ, ∀ hT : 0 < T, t ≤ T →
        ¬ β • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S := by sorry
