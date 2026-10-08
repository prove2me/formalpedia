-- Prove2me | Theorems.Thm_ConnesGreen_RG0Integration_original_picard_outer_no_strict_half_margin
-- name    : ConnesGreen.RG0Integration.original_picard_outer_no_strict_half_margin
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T22:45:28.591987+00:00
-- url     : https://prove2.me/theorems/056f09ac-3a74-48ea-a890-74fe6bd17ff0
-- title:
--   Original Picard support-right norm limit has no strict half margin under eventual failure
-- statement:
--   Let $S$ be the unchanged finite actual-zero packet and $c>0$. Suppose the original Picard markers tend in operator norm to $R$ as the support radius tends to $c$ from above, and every larger original window fails the half-bound. Then $$\forall a>\tfrac12,\quad aI\not\le R.$$ The inner Picard markers and their original pair actors are constructed, not postulated. The outer norm limit and larger-window failure are explicit premises. The theorem does not identify $c$ with a prescribed critical endpoint or decide whether the half-bound holds at $c$.
-- source:
--   monocap-tech/weil, original native companion and RG0DependencyIntegration.lean. Source/proof cuts and declarations are extracted with the Lean elaborator. Original carrier, actual zeros, multiplicities and reflected /2 custody retained.

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
import Theorems.Thm_WeilDefect_MarkerStability_no_strict_scalar_lower_bound_of_eventual_failure
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.MarkerStability ContinuousLinearMap Filter Set
open scoped InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section

theorem ConnesGreen.RG0Integration.original_picard_outer_no_strict_half_margin
    (c : ℝ) (hc : 0 < c) (S : Finset CriticalZeros)
    (R : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ))
    (hlim : Tendsto (fun T => positiveWindowPicardMarker T S)
      (nhdsWithin c (Ioi c)) (nhds R))
    (hbad : ∀ T : ℝ, ∀ hT : 0 < T, c < T →
      ¬ (1/2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S)
    (a : ℝ) (ha : (1/2 : ℝ) < a) :
    ¬ a • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ R := by sorry
