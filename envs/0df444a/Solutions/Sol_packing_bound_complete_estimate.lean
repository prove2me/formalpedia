-- Prove2me | solution 1 for packing_bound_complete_estimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/f51e037f-b493-43a8-ab86-fc7fef4c7b8b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_packing_bound_geometric_estimate
import Theorems.Thm_packing_bound_spectral_estimate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped FourierTransform ENNReal SchwartzMap BigOperators
open SpherePacking MeasureTheory Complex Real Bornology Module
variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
include d f hP hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hD_unique_covers
omit hne_zero hReal
theorem _root_.solution (hd : 0 < d) :
    ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) * (f 0).re ≥ ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) ^ 2 *
      (𝓕 f 0).re / ZLattice.covolume P.lattice volume := by
  exact
    (packing_bound_spectral_estimate (P := P) hCohnElkies₂ hD_isBounded hd).trans
      (packing_bound_geometric_estimate hRealFourier hCohnElkies₁ hP
        hD_isBounded hD_unique_covers hd)
