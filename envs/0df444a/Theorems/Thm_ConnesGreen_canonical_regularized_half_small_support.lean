-- Prove2me | Theorems.Thm_ConnesGreen_canonical_regularized_half_small_support
-- name    : ConnesGreen.canonical_regularized_half_small_support
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T04:58:06.621448+00:00
-- url     : https://prove2.me/theorems/cf17e9a1-3dcc-4cf0-a1c1-f98473c6cf04
-- title:
--   Every positive original regularization has its half-bound on the explicit interval
-- statement:
--   For 0<T<=the original positiveSupportRadius, every original finite actual-zero packet and every epsilon>0, the original regularized selected marker is at least one half the identity. The original positive covariance, selected actor and regularization parameter are unchanged.
-- source:
--   monocap-tech/weil at 28829dbeeee2ba23d6c0f3cedaf22952174099c2; unchanged exact SmallSupportPositivity.lean declarations.

import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_regularized_half_small_support (T : ℝ) (hT : 0 < T)
    (hTr : T ≤ positiveSupportRadius) (S : Finset CriticalZeros) :
    ∀ ε : ℝ, 0 < ε → (1 / 2 : ℝ) •
      (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalRegularizedMarker T hT S ε := by sorry
