-- Prove2me | solution 1 for packing_bound_geometric_estimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/962afb17-7417-4c3a-b376-b6512ddabb57

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_latticePoissonSummationFormula
import Theorems.Thm_Complex_negative_imaginary_exponential_eq_conjugate
import Theorems.Thm_SpherePacking_CohnElkies_LPBoundAux_summable_norm_on_translated_integral_lattice
import Theorems.Thm_SpherePacking_CohnElkies_packing_spectral_sum_exchange
import Theorems.Thm_SpherePacking_CohnElkies_center_double_sum_eq_region_lattice_sum
import Theorems.Thm_packing_bound_auxiliary_estimate
import Theorems.Thm_packing_bound_complete_estimate_refined

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
omit hne_zero hReal hCohnElkies₂
theorem _root_.solution (hd : 0 < d) :
    ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) * (f 0).re ≥
      (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              exp (2 * π * I *
                ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2) := by
  classical
  letI : Fintype ↑(P.centers ∩ D) :=
    P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  have hcharacter (x y : ↑(P.centers ∩ D))
      (m : SchwartzMap.polarIntegerLattice (d := d) P.lattice) :
      exp (2 * π * I *
          ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) =
        exp (2 * π * I *
          ⟪(x : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) *
          (starRingEnd ℂ)
            (exp (2 * π * I *
              ⟪(y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) := by
    have hinner :
        ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
          (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] =
          ⟪(x : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] -
          ⟪(y : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] := by
      simpa only [← RCLike.inner_eq_wInner_one] using
        (inner_sub_left
          (x : EuclideanSpace ℝ (Fin d))
          (y : EuclideanSpace ℝ (Fin d))
          (m : EuclideanSpace ℝ (Fin d)))
    rw [hinner]
    have hsplit :
        (2 * (π : ℂ) * I *
          ((⟪(x : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] -
            ⟪(y : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] : ℝ) : ℂ)) =
          2 * (π : ℂ) * I *
            (⟪(x : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] : ℂ) +
            -(2 * (π : ℂ) * I *
              (⟪(y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] : ℂ)) := by
      push_cast
      ring
    rw [hsplit, Complex.exp_add,
      Complex.negative_imaginary_exponential_eq_conjugate]
  have hfactor
      (m : SchwartzMap.polarIntegerLattice (d := d) P.lattice) :
      (∑' x : ↑(P.centers ∩ D),
        ∑' y : ↑(P.centers ∩ D),
          exp (2 * π * I *
            ⟪(x : EuclideanSpace ℝ (Fin d)) -
                (y : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) =
        (norm (∑' x : ↑(P.centers ∩ D),
          exp (2 * π * I *
            ⟪(x : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2 : ℝ) := by
    simp_rw [tsum_fintype, hcharacter]
    calc
      _ =
          (∑ x : ↑(P.centers ∩ D),
            exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
            (∑ y : ↑(P.centers ∩ D),
              (starRingEnd ℂ)
                (exp (2 * π * I *
                  ⟪(y : EuclideanSpace ℝ (Fin d)),
                    (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))) := by
            symm
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mul_sum]
      _ =
          (∑ x : ↑(P.centers ∩ D),
            exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
            (starRingEnd ℂ)
              (∑ y : ↑(P.centers ∩ D),
                exp (2 * π * I *
                  ⟪(y : EuclideanSpace ℝ (Fin d)),
                    (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) := by
            rw [map_sum]
      _ = _ := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hFourierNorm :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖) := by
    simpa using
      (SpherePacking.CohnElkies.LPBoundAux.summable_norm_on_translated_integral_lattice
        (SchwartzMap.polarIntegerLattice (d := d) P.lattice) (𝓕 f)
        (0 : EuclideanSpace ℝ (Fin d)))
  have hWeighted (x y : ↑(P.centers ∩ D)) :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        (𝓕 f m) * exp (2 * π * I *
          ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) := by
    apply Summable.of_norm
    simpa [norm_mul, Complex.norm_exp, Complex.mul_re, mul_assoc] using hFourierNorm
  have hFull :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D),
          (𝓕 f m) * exp (2 * π * I *
            ⟪(x : EuclideanSpace ℝ (Fin d)) -
                (y : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) :=
    summable_sum fun x _ => summable_sum fun y _ => hWeighted x y
  have hSpectral :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        ((𝓕 f m).re : ℂ) *
          (norm (∑' x : ↑(P.centers ∩ D),
            exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2 : ℝ)) := by
    refine (summable_congr ?_).mp hFull
    intro m
    rw [← hRealFourier (m : EuclideanSpace ℝ (Fin d)),
      ← hfactor m]
    simp [tsum_fintype, Finset.mul_sum]
  have hgeom :
      (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D))
        (ℓ : ↥P.lattice), (f (↑x - ↑y + ↑ℓ)).re) =
        (1 / ZLattice.covolume P.lattice volume) *
          ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
            (𝓕 ⇑f m).re *
              (norm (∑' x : ↑(P.centers ∩ D),
                exp (2 * π * I *
                  ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2) := by
    rw [packing_bound_complete_estimate_refined hD_isBounded hd]
    simp_rw [SchwartzMap.latticePoissonSummationFormula P.lattice f]
    simp_rw [← SchwartzMap.fourier_coe]
    rw [SpherePacking.CohnElkies.packing_spectral_sum_exchange
      f hRealFourier P hD_isBounded hd]
    simp_rw [hfactor]
    have hcov :
        (1 / (ZLattice.covolume P.lattice volume : ℂ)) =
          ((1 / ZLattice.covolume P.lattice volume : ℝ) : ℂ) := by
      norm_cast
    rw [hcov, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.re_tsum hSpectral]
    congr 1
    apply tsum_congr
    intro m
    simp only [pow_two, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  have hbound := packing_bound_auxiliary_estimate
    (f := f) hCohnElkies₁ hP hD_isBounded hd hD_unique_covers
  rw [SpherePacking.CohnElkies.center_double_sum_eq_region_lattice_sum
    (f := f) (P := P) (D := D) hD_isBounded hD_unique_covers hd] at hbound
  linarith [hgeom]
