-- Prove2me | Theorems.Thm_ConnesGreen_canonical_finite_half_cut_of_supported_negative_test
-- name    : ConnesGreen.canonical_finite_half_cut_of_supported_negative_test
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T06:03:41.840027+00:00
-- url     : https://prove2.me/theorems/10251061-b87e-4f41-a22d-66ce3f2cf476
-- title:
--   An original negative supported test forces a finite closed inner cutoff below its support window
-- statement:
--   Given an original supported selected-negative test on a positive window $t$ for the unchanged finite actual-zero packet $S$, we prove
--   $$\exists c\ge R,\quad c<t,\quad\forall T>0,\quad\tfrac12 I\le G_S(T)\ \Longleftrightarrow\ T\le c,$$
--   where $R$ is the existing positiveSupportRadius. The accepted exact original marker-half/original-test equivalence shows that the half-bound fails at the witness window $t$. Apply the accepted unconditional finite-packet half-window dichotomy. Its all-windows branch contradicts failure at $t$, so the finite closed-cutoff branch holds. Its characterization and failure at $t$ force $c<t$. This proof uses no prescribed critical-endpoint identification or right-endpoint continuity. It closes the cutoff reduction from a concrete original negative test; deriving such a test from the actual off-line quartet is a separate dependency.
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

theorem ConnesGreen.canonical_finite_half_cut_of_supported_negative_test (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g)
    (hn : ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 < 0):
    ∃ c : ℝ, positiveSupportRadius ≤ c ∧ c < t ∧
      ∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S ↔ T ≤ c) := by sorry
