-- Prove2me | solution 1 for packing_bound_complete_estimate_refined
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/6e2474f2-463c-4a06-9122-d8f3da9bd43f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_CohnElkies_LPBoundSummability_summable_lattice_shift_values

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
omit [Nonempty ↑P.centers]
include hD_isBounded
theorem _root_.solution (hd : 0 < d) :
    ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : ↥P.lattice), (f (↑x - ↑y + ↑ℓ)).re =
    (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : ↥P.lattice), f (↑x - ↑y + ↑ℓ)).re := by
  haveI : Finite ↑(P.centers ∩ D) := finite_centers_in_bounded_region P D hD_isBounded hd
  rw [re_tsum Summable.of_finite]
  refine tsum_congr fun x => ?_
  rw [re_tsum Summable.of_finite]
  refine tsum_congr fun y => ?_
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using!
    (re_tsum
        (SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_shift_values (Λ := P.lattice)
          (f := f) (a := (↑x - ↑y : EuclideanSpace ℝ (Fin d))))).symm
