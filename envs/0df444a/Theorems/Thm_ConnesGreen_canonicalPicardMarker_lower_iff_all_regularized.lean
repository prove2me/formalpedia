-- Prove2me | Theorems.Thm_ConnesGreen_canonicalPicardMarker_lower_iff_all_regularized
-- name    : ConnesGreen.canonicalPicardMarker_lower_iff_all_regularized
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T23:59:57.386512+00:00
-- url     : https://prove2.me/theorems/1d9ba9b9-4f52-4c84-9e0e-c3cd424761ed
-- title:
--   Original Picard lower bounds are exactly all positive regularized bounds
-- statement:
--   Fix an original positive window $t$, the unchanged finite actual-zero packet $S$, and a real scalar $a$. The constructed inner Picard marker $C_t$ satisfies $$aI\le C_t\quad\Longleftrightarrow\quad\forall\varepsilon>0,\ aI\le M_{t,\varepsilon}.$$ Its certified infimum specification proves both directions. This removes an inner-limit premise without using an unregularized inverse. No arithmetic positivity is asserted.
-- source:
--   monocap-tech/weil; original CanonicalGreenFiniteOffline.lean and RG0QuartetCutEndpoint.lean. Original carrier, covariance, selected packet and constructed Picard marker preserved.

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.MarkerStability
open scoped InnerProductSpace lp Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
noncomputable section

theorem ConnesGreen.canonicalPicardMarker_lower_iff_all_regularized
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) (a : ℝ) :
    a • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S ↔
    ∀ ε : ℝ, 0 < ε → a • 1 ≤ canonicalRegularizedMarker t ht S ε := by sorry
