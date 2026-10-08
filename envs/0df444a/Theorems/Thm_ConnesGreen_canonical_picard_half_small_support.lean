-- Prove2me | Theorems.Thm_ConnesGreen_canonical_picard_half_small_support
-- name    : ConnesGreen.canonical_picard_half_small_support
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T04:56:05.208545+00:00
-- url     : https://prove2.me/theorems/e43c0d33-ecb9-488c-9862-801dc63d4886
-- title:
--   The original selected Picard marker has its half-bound on the explicit interval
-- statement:
--   For 0<T<=the original positiveSupportRadius and every original finite actual-zero packet, its original inner Picard marker is at least one half the identity on the unchanged selected coefficient space. No critical-endpoint identification or RH assumption is made.
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

theorem ConnesGreen.canonical_picard_half_small_support (T : ℝ) (hT : 0 < T)
    (hTr : T ≤ positiveSupportRadius) (S : Finset CriticalZeros) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S := by sorry
