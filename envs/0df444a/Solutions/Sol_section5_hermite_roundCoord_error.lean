-- Prove2me | solution 1 for section5_hermite_roundCoord_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:16:16.43472+00:00
-- url     : https://prove2.me/submissions/d60fd1d7-73a0-4a18-bf7a-794bc6ae0a1d

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5CellQuadrature
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Mathlib
import Theorems.Thm_Aux_w_53_hermite_hasDerivAt_h1D
import Theorems.Thm_Aux_w_53_hermite_hasDerivAt_phi
import Theorems.Thm_Aux_w_53_hermite_x_mul_h1D_eq
import Theorems.Thm_section5_grid_cell_quadrature
import Theorems.Thm_section5_grid_sampling_integral
import Theorems.Thm_section5_hermite_deriv_integrable_sq
import Theorems.Thm_section5_hermite_derivative_energy
section
set_option autoImplicit false

open MeasureTheory Aux_w_53_hermite

/-! The normalized Hermite functions and the derivative estimate required by Appendix D. -/











theorem section5_gaussian_amplitude_derivative (x : ℝ) :
    HasDerivAt (fun y => Real.sqrt (phi y)) (-x/2 * Real.sqrt (phi x)) x := by
  convert (hasDerivAt_phi x).sqrt (phi_pos x).ne' using 1
  have hs : Real.sqrt (phi x) ≠ 0 := (Real.sqrt_pos.mpr (phi_pos x)).ne'
  symm
  calc
    _ = -x*(Real.sqrt (phi x))^2/(2*Real.sqrt (phi x)) := by
      rw [Real.sq_sqrt (phi_pos x).le]
    _ = _ := by field_simp

theorem section5_hermite_wave_derivative (k : ℕ) (x : ℝ) :
    HasDerivAt (section5_hermite_wave k)
      (((if k=0 then 0 else Real.sqrt k * section5_hermite_wave (k-1) x) -
          Real.sqrt (k+1) * section5_hermite_wave (k+1) x)/2) x := by
  have h := (section5_gaussian_amplitude_derivative x).mul (hasDerivAt_h1D k x)
  change HasDerivAt (section5_hermite_wave k) _ x at h
  apply h.congr_deriv
  have hx := x_mul_h1D_eq k x
  unfold section5_hermite_wave h1D_deriv
  split_ifs with hk <;> simp only [hk, ↓reduceIte] at hx
  · subst k
    calc
      _ = -Real.sqrt (phi x)/2 * (x*h1D 0 x) := by ring
      _ = _ := by rw [hx]; ring
  · calc
      _ = Real.sqrt (phi x)/2 *
        (2*(Real.sqrt k*h1D (k-1) x) - x*h1D k x) := by ring
      _ = _ := by rw [hx]; ring















theorem section5_hermite_series_hasDerivAt {D : ℕ} (c : Fin D → ℝ) (x : ℝ) :
    HasDerivAt (section5_hermite_series c) (section5_hermite_series_deriv c x) x := by
  have h := HasDerivAt.sum (u := Finset.univ)
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin D))) =>
      (section5_hermite_wave_derivative k x).const_mul (c k))
  have hfun : (∑ i : Fin D, fun y => c i*section5_hermite_wave i y) =
      section5_hermite_series c := by
    funext y
    simp only [Finset.sum_apply, section5_hermite_series]
  rw [hfun] at h
  apply h.congr_deriv
  unfold section5_hermite_series_deriv section5_hermite_lower section5_hermite_upper
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hzero : (k:ℕ)=0
  · simp [hzero]
    ring
  · simp only [if_neg hzero]
    ring

theorem section5_hermite_series_deriv_continuous {D : ℕ} (c : Fin D → ℝ) :
    Continuous (section5_hermite_series_deriv c) := by
  unfold section5_hermite_series_deriv section5_hermite_lower section5_hermite_upper
  exact ((continuous_finsetSum _ (fun k _ => continuous_const.mul
    (section5_hermite_wave_continuous _))).sub
      (continuous_finsetSum _ (fun k _ => continuous_const.mul
        (section5_hermite_wave_continuous _)))).div_const _











theorem section5_hermite_series_continuous {D : ℕ} (c : Fin D → ℝ) :
    Continuous (section5_hermite_series c) :=
  continuous_finsetSum _ (fun k _ => continuous_const.mul (section5_hermite_wave_continuous _))











theorem section5_hermite_cell_sampling_error {D : ℕ} (c : Fin D → ℝ)
    (a δ : ℝ) (hδ : 0 ≤ δ) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      ∫ x in (a+j*δ)..(a+(j+1)*δ),
        ‖section5_hermite_series c x-section5_hermite_series c (a+j*δ)‖^2) ≤
      δ^2*(D+1)*∑ k, (c k)^2 := by
  have h := section5_grid_cell_quadrature (section5_hermite_series c)
    (section5_hermite_series_deriv c) (section5_hermite_series_hasDerivAt c)
    (section5_hermite_series_deriv_continuous c) a δ hδ N
  have hab : a ≤ a+(N:ℝ)*δ := by
    have := mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) hδ
    linarith
  have hi : (∫ y in a..(a+N*δ), ‖section5_hermite_series_deriv c y‖^2) ≤
      ∫ y : ℝ, (section5_hermite_series_deriv c y)^2 := by
    simp only [Real.norm_eq_abs, sq_abs]
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_le_integral (section5_hermite_deriv_integrable_sq c)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  calc
    _ ≤ _ := h
    _ ≤ δ^2 * ((D+1)*∑ k, (c k)^2) :=
      mul_le_mul_of_nonneg_left (hi.trans (section5_hermite_derivative_energy c)) (sq_nonneg δ)
    _ = _ := by ring



theorem section5_complex_hermite_series_re {D : ℕ} (c : Fin D → ℂ) (x : ℝ) :
    (section5_complex_hermite_series c x).re = section5_hermite_series (fun k => (c k).re) x := by
  simp [section5_complex_hermite_series, section5_hermite_series, Complex.mul_re]

theorem section5_complex_hermite_series_im {D : ℕ} (c : Fin D → ℂ) (x : ℝ) :
    (section5_complex_hermite_series c x).im = section5_hermite_series (fun k => (c k).im) x := by
  simp [section5_complex_hermite_series, section5_hermite_series, Complex.mul_im]

theorem section5_complex_hermite_series_continuous {D : ℕ} (c : Fin D → ℂ) :
    Continuous (section5_complex_hermite_series c) := by
  unfold section5_complex_hermite_series
  exact continuous_finsetSum _ (fun k _ => continuous_const.mul
    (Complex.continuous_ofReal.comp (section5_hermite_wave_continuous _)))

theorem section5_complex_hermite_error_sq {D : ℕ} (c : Fin D → ℂ) (x y : ℝ) :
    ‖section5_complex_hermite_series c x-section5_complex_hermite_series c y‖^2 =
      (section5_hermite_series (fun k => (c k).re) x-
        section5_hermite_series (fun k => (c k).re) y)^2+
      (section5_hermite_series (fun k => (c k).im) x-
        section5_hermite_series (fun k => (c k).im) y)^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, section5_complex_hermite_series_re,
    section5_complex_hermite_series_im, pow_two]

theorem section5_complex_hermite_cell_error {D : ℕ} (c : Fin D → ℂ)
    (a δ : ℝ) (hδ : 0 ≤ δ) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      ∫ x in (a+j*δ)..(a+(j+1)*δ),
        ‖section5_complex_hermite_series c x-section5_complex_hermite_series c (a+j*δ)‖^2) ≤
      δ^2*(D+1)*∑ k, ‖c k‖^2 := by
  let cr := fun k => (c k).re
  let ci := fun k => (c k).im
  have hr := section5_hermite_cell_sampling_error cr a δ hδ N
  have hi := section5_hermite_cell_sampling_error ci a δ hδ N
  simp only [Real.norm_eq_abs, sq_abs] at hr hi
  have heq : (∑ j ∈ Finset.range N,
      ∫ x in (a+j*δ)..(a+(j+1)*δ),
        ‖section5_complex_hermite_series c x-section5_complex_hermite_series c (a+j*δ)‖^2) =
      (∑ j ∈ Finset.range N, ∫ x in (a+j*δ)..(a+(j+1)*δ),
        (section5_hermite_series cr x-section5_hermite_series cr (a+j*δ))^2)+
      (∑ j ∈ Finset.range N, ∫ x in (a+j*δ)..(a+(j+1)*δ),
        (section5_hermite_series ci x-section5_hermite_series ci (a+j*δ))^2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp_rw [section5_complex_hermite_error_sq]
    apply intervalIntegral.integral_add
    · exact (((section5_hermite_series_continuous cr).sub continuous_const).pow 2).intervalIntegrable _ _
    · exact (((section5_hermite_series_continuous ci).sub continuous_const).pow 2).intervalIntegrable _ _
  rw [heq]
  calc
    _ ≤ δ^2*(D+1)*(∑ k, (cr k)^2)+δ^2*(D+1)*(∑ k, (ci k)^2) := add_le_add hr hi
    _ = _ := by
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      change (c k).re^2+(c k).im^2 = ‖c k‖^2
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring

/-- The one-dimensional complex-coefficient sampling estimate (Appendix D, Eq. 226),
with exactly the paper's constant and lattice spacing. -/
theorem section5_hermite_sampling_226 {D : ℕ} (c : Fin D → ℂ)
    (a : ℝ) (M N : ℕ) (hM : 0 < M) :
    let δ := Real.sqrt (4*Real.pi/M)
    (∑ j ∈ Finset.range N,
      ∫ x in (a+j*δ)..(a+(j+1)*δ),
        ‖section5_complex_hermite_series c x-section5_complex_hermite_series c (a+j*δ)‖^2) ≤
      16*(D+1)/M*∑ k, ‖c k‖^2 := by
  dsimp only
  have h := section5_complex_hermite_cell_error c a (Real.sqrt (4*Real.pi/M))
    (Real.sqrt_nonneg _) N
  rw [Real.sq_sqrt (by positivity)] at h
  apply h.trans
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hM']
  nlinarith [Real.pi_lt_four, (Nat.cast_nonneg D : (0:ℝ) ≤ D)]







end
set_option autoImplicit false
open MeasureTheory Aux_w_53_hermite

theorem solution {D : ℕ} (c : Fin D → ℂ)
    (M : ℕ) (hM : 0 < M) :
    (∫ x in (-QuantumLTF.Example.gridRadius M)..(QuantumLTF.Example.gridRadius M),
      ‖section5_complex_hermite_series c x-
        section5_complex_hermite_series c (QuantumLTF.Example.roundCoord M x)‖^2) ≤
          16*(D+1)/M*∑ k, ‖c k‖^2 := by
  have hδ : 0 < QuantumLTF.Example.gridSpacing M := by
    unfold QuantumLTF.Example.gridSpacing
    positivity
  have hsamp (x : ℝ) : section5_grid_sample (-QuantumLTF.Example.gridRadius M)
      (QuantumLTF.Example.gridSpacing M) x = QuantumLTF.Example.roundCoord M x := by
    simp only [section5_grid_sample, QuantumLTF.Example.roundCoord, sub_neg_eq_add]
  have hend : -QuantumLTF.Example.gridRadius M+M*QuantumLTF.Example.gridSpacing M =
      QuantumLTF.Example.gridRadius M := by unfold QuantumLTF.Example.gridRadius; ring
  have hh := section5_grid_sampling_integral (section5_complex_hermite_series c)
    (section5_complex_hermite_series_continuous c) (-QuantumLTF.Example.gridRadius M)
    (QuantumLTF.Example.gridSpacing M) hδ M
  simp_rw [hsamp, hend] at hh
  rw [hh]
  exact section5_hermite_sampling_226 c (-QuantumLTF.Example.gridRadius M) M M hM
