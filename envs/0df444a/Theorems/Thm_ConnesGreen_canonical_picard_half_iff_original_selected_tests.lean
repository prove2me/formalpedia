-- Prove2me | Theorems.Thm_ConnesGreen_canonical_picard_half_iff_original_selected_tests
-- name    : ConnesGreen.canonical_picard_half_iff_original_selected_tests
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T00:16:58.285079+00:00
-- url     : https://prove2.me/theorems/a9410505-7822-44d8-b2ab-e12a31aa0860
-- title:
--   Original inner half-bound is exactly original selected-test nonnegativity
-- statement:
--   For every positive original support window $T$ and unchanged finite actual-zero packet $S$, let $C_{T,S}$ be the constructed original inner Picard marker, $P_T$ the complete original positive synthesis, and $N_{T,S}$ the original selected synthesis. Then $$\tfrac12I\le C_{T,S}\quad\Longleftrightarrow\quad\forall g\text{ original admissible at }T,\ \|P_T^*\operatorname{sourceEmbed}_T(Lg)\|^2-\|N_{T,S}^*\operatorname{sourceEmbed}_T(Lg)\|^2\ge0.$$ The accepted original inner half-bound/covariance equivalence and accepted original dense-test covariance criterion prove this. The quadratic expression is exactly the native selectedQuadratic definition expanded, not a new form. Actual zeros, analytic multiplicities, reflected pair normalization, physical metric, selected packet and the constructed inner limit are unchanged. The equivalence asserts neither side unconditionally, supplies no arithmetic endpoint jump budget, and does not establish RH.
-- source:
--   monocap-tech/weil at 7c5b1bc48d1cd2dd7385b1e634cd33a1e95550c7. CanonicalGreenTestDensity.lean, CanonicalGreenQuadraticEndpoint.lean and CriticalWindowBoundary.lean. Exact native definitions are unfolded only where no separate platform definition exists; native Lean checks these public statements against the originals.

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

theorem ConnesGreen.canonical_picard_half_iff_original_selected_tests (T : ℝ) (hT : 0 < T)
    (S : Finset CriticalZeros) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S ↔
    ∀ g : ℝ → ℂ, SupportedTest T g →
      0 ≤ ‖(canonicalPositiveSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 -
        ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 := by sorry
