-- Prove2me | Theorems.Thm_ConnesGreen_canonical_actor_test_norms_window_independent
-- name    : ConnesGreen.canonical_actor_test_norms_window_independent
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T00:30:22.062667+00:00
-- url     : https://prove2.me/theorems/824681a7-e642-4f6e-962c-c457919c8cd4
-- title:
--   Original actor test energies are independent of the containing window
-- statement:
--   Let $t,T>0$, let $S$ be an unchanged finite packet of actual critical-strip zeta zeros, and let the same original admissible test $g$ be supported in both windows. Its full original positive analysis energy and original selected negative analysis energy are equal in the two ORIGINAL physical carriers: $$\|P_T^*\operatorname{sourceEmbed}_T(Lg)\|^2=\|P_t^*\operatorname{sourceEmbed}_t(Lg)\|^2,\qquad\|N_{T,S}^*\operatorname{sourceEmbed}_T(Lg)\|^2=\|N_{t,S}^*\operatorname{sourceEmbed}_t(Lg)\|^2.$$ Apply the accepted original actor inclusion in the direction of the smaller window. Its adjoint compression identities, after taking adjoints again, identify the analysis vectors on the preserved source. The opposite window order follows by symmetry. No ordering hypothesis is added to the statement, and no positivity or arithmetic endpoint bound is assumed.
-- source:
--   monocap-tech/weil at 5999649ed66d79a903f2d0dceca4a8c37093fe71. Exact native signatures from CanonicalGreenMarkerMargin.lean and CriticalWindowBoundary.lean; the energy proof additionally cross-validates the original actor-inclusion API. Native declarations and statements are unchanged.

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

theorem ConnesGreen.canonical_actor_test_norms_window_independent (t T : ℝ) (ht : 0 < t)
    (hT : 0 < T) (S : Finset CriticalZeros) (g : ℝ → ℂ)
    (hg : SupportedTest t g) (hgT : SupportedTest T g) :
    ‖(canonicalPositiveSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 =
      ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ∧
    ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 =
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 := by sorry
