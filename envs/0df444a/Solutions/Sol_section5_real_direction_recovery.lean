-- Prove2me | solution 1 for section5_real_direction_recovery
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:51.438898+00:00
-- url     : https://prove2.me/submissions/1e703c40-8f8a-470d-b531-cb0d4008aaa4

import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Mathlib
import Theorems.Thm_section5_normalize_real_direction
section
set_option autoImplicit false







theorem section5_parts_norm_sq {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖section5_real_part v‖^2 + ‖section5_imag_part v‖^2 = ‖v‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, section5_real_part, section5_imag_part,
    WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem section5_real_part_contraction {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖section5_real_part v‖ ≤ ‖v‖ := by
  have hh : ‖section5_real_part v‖^2 ≤ ‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i hi
    change ‖(v i).re‖^2 ≤ ‖v i‖^2
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  nlinarith [norm_nonneg (section5_real_part v), norm_nonneg v]

theorem section5_imag_part_contraction {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖section5_imag_part v‖ ≤ ‖v‖ := by
  have hh : ‖section5_imag_part v‖^2 ≤ ‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i hi
    change ‖(v i).im‖^2 ≤ ‖v i‖^2
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2
  nlinarith [norm_nonneg (section5_imag_part v), norm_nonneg v]



end
set_option autoImplicit false
theorem solution {n : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) (w : EuclideanSpace ℝ (Fin n))
    (ζ : ℂ) (ε : ℝ) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hε : 0 < ε) (hε' : ε < 1)
    (hclose : ‖v - ζ • section5_complexify w‖ ≤ ε/24) :
    let a := section5_real_part v
    let b := section5_imag_part v
    let r := if ‖b‖ ≤ ‖a‖ then a else b
    r ≠ 0 ∧
      (‖‖r‖⁻¹ • r - w‖ ≤ ε/6 ∨ ‖‖r‖⁻¹ • r + w‖ ≤ ε/6) := by
  classical
  let a := section5_real_part v
  let b := section5_imag_part v
  let r := if ‖b‖ ≤ ‖a‖ then a else b
  let c : ℝ := if ‖b‖ ≤ ‖a‖ then ζ.re else ζ.im
  have hparts : ‖a‖^2 + ‖b‖^2 = 1 := by
    simpa [a, b, hv] using section5_parts_norm_sq v
  have hbig : 2/3 < ‖r‖ := by
    dsimp [r]
    split_ifs with h
    · nlinarith [norm_nonneg a, norm_nonneg b]
    · push Not at h
      nlinarith [norm_nonneg a, norm_nonneg b]
  have hrc : ‖r - c • w‖ ≤ ε/24 := by
    have hre : section5_real_part (v - ζ • section5_complexify w) = a - ζ.re • w := by
      ext i
      simp [section5_real_part, section5_complexify, a, Complex.mul_re]
    have him : section5_imag_part (v - ζ • section5_complexify w) = b - ζ.im • w := by
      ext i
      simp [section5_imag_part, section5_complexify, b, Complex.mul_im]
    dsimp [r, c]
    split_ifs
    · rw [← hre]
      exact (section5_real_part_contraction _).trans hclose
    · rw [← him]
      exact (section5_imag_part_contraction _).trans hclose
  have hc : 1/2 < |c| := by
    have hh := norm_sub_norm_le r (c • w)
    rw [norm_smul, hw, Real.norm_eq_abs, mul_one] at hh
    linarith
  obtain ⟨hr, hresult⟩ := section5_normalize_real_direction r w c (ε/24) hw hc
    (by positivity) (by linarith) hrc
  change r ≠ 0 ∧ _
  refine ⟨hr, ?_⟩
  change ‖‖r‖⁻¹ • r - w‖ ≤ ε/6 ∨ ‖‖r‖⁻¹ • r + w‖ ≤ ε/6
  have hconst : 4*(ε/24) = ε/6 := by ring
  rw [hconst] at hresult
  rcases lt_or_gt_of_ne (abs_pos.mp (show 0 < |c| by linarith)) with hneg | hpos
  · right
    simpa [sign_neg hneg, sub_eq_add_neg] using hresult
  · left
    simpa [sign_pos hpos] using hresult
