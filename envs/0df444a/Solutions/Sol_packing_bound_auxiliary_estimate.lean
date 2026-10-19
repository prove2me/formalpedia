-- Prove2me | solution 1 for packing_bound_auxiliary_estimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/c35f1978-a8b4-4bf5-b6a1-60502c726995

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_CohnElkies_center_double_sum_eq_region_lattice_sum
import Theorems.Thm_SpherePacking_CohnElkies_real_lattice_sum_bounded_by_origin_term

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
include hP hCohnElkies₁
open Classical
theorem _root_.solution (hd : 0 < d)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) :
    ∑' x : P.centers, ∑' y : ↑(P.centers ∩ D), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re
      ≤ ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) * (f 0).re := by
  letI := P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  rw [SpherePacking.CohnElkies.center_double_sum_eq_region_lattice_sum
    f P hD_isBounded hD_unique_covers hd]
  simp_rw [tsum_fintype]
  calc
    (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D),
      ∑' ℓ : P.lattice,
        (f ((x : EuclideanSpace ℝ (Fin d)) -
          (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
      ≤ ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D),
          ite (x = y) (f 0).re 0 := by
            exact Finset.sum_le_sum fun x _ =>
              Finset.sum_le_sum fun y _ =>
                SpherePacking.CohnElkies.real_lattice_sum_bounded_by_origin_term
                  hP hD_unique_covers hCohnElkies₁ x y
    _ = ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) *
          (f 0).re := by
            simp [PeriodicSpherePacking.boundedCenterRepresentativeCount]
