-- Prove2me | solution 1 for packing_bound_spectral_estimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/10344d5c-6f06-41ec-bc4f-7e51170f81e1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_lattice_covolume_eq_coordinate_determinant
import Theorems.Thm_SpherePacking_CohnElkies_LPBoundAux_summable_norm_on_translated_integral_lattice
import Theorems.Thm_SpherePacking_CohnElkies_origin_character_sum_norm_sq_eq_orbit_count_sq
import Theorems.Thm_SpherePacking_CohnElkies_nonnegative_weighted_nonzero_frequency_sum

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
include d f hP hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂
omit hne_zero hReal hRealFourier hCohnElkies₁ hP [Nonempty ↑P.centers]
theorem _root_.solution (hd : 0 < d) :
    (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              exp (2 * π * I *
                ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)
      ≥
      ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) ^ 2 * (𝓕 f 0).re / ZLattice.covolume P.lattice volume := by
  classical
  letI := P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  let N : ℝ := P.boundedCenterRepresentativeCount hd hD_isBounded
  let F : SchwartzMap.polarIntegerLattice (d := d) P.lattice → ℝ :=
    fun m =>
      (𝓕 ⇑f m).re *
        (norm (∑' x : ↑(P.centers ∩ D),
          exp (2 * π * I *
            ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)
  have hFourierNorm :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖) := by
    simpa using
      (SpherePacking.CohnElkies.LPBoundAux.summable_norm_on_translated_integral_lattice
        (SchwartzMap.polarIntegerLattice (d := d) P.lattice) (𝓕 f)
        (0 : EuclideanSpace ℝ (Fin d)))
  have hCharacterBound (m : SchwartzMap.polarIntegerLattice (d := d) P.lattice) :
      norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I *
          ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ≤ N := by
    rw [tsum_fintype]
    calc
      _ ≤ ∑ x : ↑(P.centers ∩ D),
        ‖exp (2 * π * I *
          ⟪(x : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])‖ := norm_sum_le _ _
      _ = N := by
        simp [N, PeriodicSpherePacking.boundedCenterRepresentativeCount,
          Complex.norm_exp, Complex.mul_re, mul_assoc]
  have hFnonneg (m : SchwartzMap.polarIntegerLattice (d := d) P.lattice) :
      0 ≤ F m := by
    exact mul_nonneg (hCohnElkies₂ _) (sq_nonneg _)
  have hFsummable : Summable F := by
    refine Summable.of_nonneg_of_le hFnonneg (fun m => ?_)
      (hFourierNorm.mul_left (N ^ 2))
    have hcoeff :
        (𝓕 ⇑f (m : EuclideanSpace ℝ (Fin d))).re ≤
          ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖ := by
      exact (le_abs_self _).trans
        (Complex.abs_re_le_norm ((𝓕 f) (m : EuclideanSpace ℝ (Fin d))))
    have hsq :
        norm (∑' x : ↑(P.centers ∩ D),
          exp (2 * π * I *
            ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2 ≤ N ^ 2 := by
      have hN : 0 ≤ N := by
        dsimp [N]
        positivity
      nlinarith [hCharacterBound m, norm_nonneg
        (∑' x : ↑(P.centers ∩ D),
          exp (2 * π * I *
            ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))]
    change _ ≤ N ^ 2 * ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖
    simpa [F, mul_comm] using
      (mul_le_mul hcoeff hsq (sq_nonneg _) (norm_nonneg _))
  have htail :
      0 ≤ ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
        if m = 0 then 0 else F m := by
    exact SpherePacking.CohnElkies.nonnegative_weighted_nonzero_frequency_sum
      f P D hCohnElkies₂
  have horigin :
      F (0 : SchwartzMap.polarIntegerLattice (d := d) P.lattice) =
        (𝓕 f 0).re * N ^ 2 := by
    change (𝓕 f (0 : EuclideanSpace ℝ (Fin d))).re *
      norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I *
          ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2 =
      (𝓕 f 0).re * N ^ 2
    rw [SpherePacking.CohnElkies.origin_character_sum_norm_sq_eq_orbit_count_sq
      P hd hD_isBounded]
  have hsum : (𝓕 f 0).re * N ^ 2 ≤ ∑' m, F m := by
    rw [hFsummable.tsum_eq_add_tsum_ite 0, horigin]
    linarith
  have hcovol : 0 ≤ ZLattice.covolume P.lattice volume := by
    rw [SchwartzMap.lattice_covolume_eq_coordinate_determinant]
    exact abs_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ (1 / ZLattice.covolume P.lattice volume : ℝ))
  simpa [F, N, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
