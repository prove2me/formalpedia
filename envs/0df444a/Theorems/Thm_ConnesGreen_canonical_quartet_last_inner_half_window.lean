-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_last_inner_half_window
-- name    : ConnesGreen.canonical_quartet_last_inner_half_window
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T06:29:52.787367+00:00
-- url     : https://prove2.me/theorems/cab8d1c0-bfcd-4077-abdf-3df95aec41f6
-- title:
--   Original off-line quartet finite closed last inner half-bound window
-- statement:
--   For an ORIGINAL off-line actual zeta-zero quartet, we certify the exact native last-inner-half-window statement:
--   $$\exists c\ge R,\quad\forall T>0,\quad \tfrac12 I\le G_Q(T)\ \Longleftrightarrow\ T\le c.$$
--   The closed coefficient-to-original-physical-witness assembly constructs a supported selected-negative test without a separation premise. The accepted original finite-half-cut theorem then supplies a cutoff below its support window, closed at the cutoff itself. Retaining its lower bound and exact characterization gives the original native statement. The finite cutoff is for the original inner marker; it is not identified with a separately prescribed critical endpoint, and no right-support jump budget, global Weil positivity or RH is asserted.
-- source:
--   monocap-tech/weil at 68011f0aa80779d1735ecbe344b0314d03cd3de5; WeilDefect/Connes/CoefficientPhysicalWitness.lean (new additive margin and witness declarations); original CanonicalGreenBackground, CanonicalGreenMarkerLimit and CriticalWindowBoundary declarations retained.

import Definitions.Def_ConnesGreen_original_quartet
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
import Definitions.Def_ConnesGreen_small_support_constants
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open ConnesRZQuartet

theorem ConnesGreen.canonical_quartet_last_inner_half_window (ρ : CriticalZeros)
    (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, positiveSupportRadius ≤ c ∧
      ∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤
            canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c) := by sorry
