-- Prove2me | Theorems.Thm_ConnesGreen_canonical_picard_half_of_all_smaller_windows
-- name    : ConnesGreen.canonical_picard_half_of_all_smaller_windows
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T00:30:41.524207+00:00
-- url     : https://prove2.me/theorems/8e88977c-77a0-44f6-8316-6394674eb169
-- title:
--   Original inner half-bound closes at its left boundary
-- statement:
--   For an original positive window $T$ and unchanged finite actual-zero packet $S$, suppose the constructed ORIGINAL inner Picard marker has the half-bound at every positive strictly smaller window. Then $$\Big(\forall\,0<t<T,\ \tfrac12I\le C_{t,S}\Big)\quad\Longrightarrow\quad\tfrac12I\le C_{T,S}.$$ Every unchanged original admissible test at $T$ fits a strictly smaller positive window by the accepted compact-support lemma. The accepted original dense-test half-bound equivalence supplies its selected-test nonnegativity there. The accepted window-energy identities transport both original actor energies back to $T$, and the same test criterion proves the half-bound at $T$. This is the exact native conditional closure theorem, not unconditional arithmetic positivity. No right-limit continuity, endpoint jump budget, critical-endpoint identification, neutral-shell attainment, or RH is asserted.
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

theorem ConnesGreen.canonical_picard_half_of_all_smaller_windows (T : ℝ) (hT : 0 < T)
    (S : Finset CriticalZeros)
    (hsmall : ∀ t : ℝ, ∀ ht : 0 < t, t < T →
      (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S := by sorry
