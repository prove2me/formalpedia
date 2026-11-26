-- Prove2me | solution 1 for exists_polynomial_separator_of_isCompact_nonempty_convex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:06.778613+00:00
-- url     : https://prove2.me/submissions/ba9a8b3b-cf3d-4e4e-bbcc-642e73a4d2e7

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.UniformConvergence
import Definitions.Def_Operator_Crouzeix_ConvexRunge
section
open Complex Filter Metric Set
open scoped Topology
private theorem affine_norm_sq (a : ℝ) (y : ℂ) :
    ‖1 + (a : ℂ) * y‖ ^ 2 =
      1 + 2 * a * y.re + a ^ 2 * ‖y‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm,
    Complex.normSq_apply]
  norm_num only [Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.one_im,
    Complex.mul_im]
  ring
private theorem exists_affine_contraction
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (hconvex : Convex ℝ K) {ζ : ℂ} (hζ : ζ ∉ K) :
    ∃ (a : ℝ) (lam : ℂ) (r : ℝ),
      0 < a ∧ lam ≠ 0 ∧ 0 ≤ r ∧ r < 1 ∧
        ∀ z ∈ K, ‖1 + (a : ℂ) * lam * (z - ζ)‖ ≤ r := by
  obtain ⟨f, u, hfK, hfζ⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      hconvex hK.isClosed hζ
  change (∀ z ∈ K, (f z).re < u) at hfK
  change u < (f ζ).re at hfζ
  let lam : ℂ := f 1
  have hf_apply (z : ℂ) : f z = z * lam := by
    calc
      f z = f (z • (1 : ℂ)) := by simp only [smul_eq_mul, mul_one]
      _ = z • f 1 := map_smul f z 1
      _ = z * lam := by simp only [smul_eq_mul, lam]
  obtain ⟨z0, hz0⟩ := hne
  have hlam : lam ≠ 0 := by
    intro hlam_zero
    have hz0_zero : f z0 = 0 := by
      rw [hf_apply, hlam_zero, mul_zero]
    have hζ_zero : f ζ = 0 := by
      rw [hf_apply, hlam_zero, mul_zero]
    have hleft := hfK z0 hz0
    rw [hz0_zero] at hleft
    rw [hζ_zero] at hfζ
    norm_num only [Complex.zero_re] at hleft hfζ
    linarith only [hleft, hfζ]
  let δ : ℝ := (f ζ).re - u
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact sub_pos.mpr hfζ
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hR_nonneg : 0 ≤ R := by
    have hz0_bound := hR hz0
    rw [Metric.mem_closedBall, dist_zero_right] at hz0_bound
    exact (norm_nonneg z0).trans hz0_bound
  let B : ℝ := ‖lam‖ * (R + ‖ζ‖)
  have hB_nonneg : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hy_bound (z : ℂ) (hz : z ∈ K) : ‖lam * (z - ζ)‖ ≤ B := by
    rw [norm_mul]
    calc
      ‖lam‖ * ‖z - ζ‖ ≤ ‖lam‖ * (‖z‖ + ‖ζ‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le z ζ) (norm_nonneg lam)
      _ ≤ ‖lam‖ * (R + ‖ζ‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg lam)
        apply add_le_add
        have hz_bound := hR hz
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz_bound
        exact le_rfl
      _ = B := rfl
  have hy_re (z : ℂ) (hz : z ∈ K) :
      (lam * (z - ζ)).re < -δ := by
    have hid : lam * (z - ζ) = f z - f ζ := by
      rw [hf_apply z, hf_apply ζ]
      ring
    rw [hid, Complex.sub_re]
    dsimp only [δ]
    linarith only [hfK z hz]
  let a : ℝ := δ / (B ^ 2 + 1)
  have hden : 0 < B ^ 2 + 1 := by positivity
  have ha : 0 < a := by
    dsimp only [a]
    exact div_pos hδ hden
  have ha_eq : a * (B ^ 2 + 1) = δ := by
    dsimp only [a]
    exact div_mul_cancel₀ δ (ne_of_gt hden)
  have haB : a * B ^ 2 < δ := by
    nlinarith only [ha_eq, ha]
  have hw_lt (z : ℂ) (hz : z ∈ K) :
      ‖1 + (a : ℂ) * lam * (z - ζ)‖ < 1 := by
    let y : ℂ := lam * (z - ζ)
    have hy_norm := hy_bound z hz
    have hy_sq : ‖y‖ ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ (norm_nonneg y) hB_nonneg).2 hy_norm
    have hy_real := hy_re z hz
    have hlinear : a * y.re < -(a * δ) := by
      simpa only [y, mul_neg] using mul_lt_mul_of_pos_left hy_real ha
    have hquad : a ^ 2 * ‖y‖ ^ 2 ≤ a ^ 2 * B ^ 2 :=
      mul_le_mul_of_nonneg_left hy_sq (sq_nonneg a)
    have htail : a ^ 2 * B ^ 2 < a * δ := by
      have hsmall := mul_lt_mul_of_pos_left haB ha
      nlinarith only [hsmall]
    apply (sq_lt_sq₀ (norm_nonneg _) zero_le_one).1
    rw [show (a : ℂ) * lam * (z - ζ) = (a : ℂ) * y by
      dsimp only [y]
      ring,
      affine_norm_sq]
    nlinarith only [hlinear, hquad, htail, mul_pos ha hδ]
  let w : ℂ → ℝ := fun z => ‖1 + (a : ℂ) * lam * (z - ζ)‖
  have hw_continuous : Continuous w := by
    dsimp only [w]
    fun_prop
  obtain ⟨zmax, hzmax, hmax⟩ :=
    hK.exists_isMaxOn ⟨z0, hz0⟩ hw_continuous.continuousOn
  refine ⟨a, lam, w zmax, ha, hlam, norm_nonneg _, hw_lt zmax hzmax, ?_⟩
  intro z hz
  exact hmax hz
end

set_option autoImplicit false
open Complex Filter Metric Set
open scoped Topology
theorem _root_.solution
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (hconvex : Convex ℝ K) {ζ : ℂ} (hζ : ζ ∉ K) :
    ∃ (p : Polynomial ℂ) (r : ℝ),
      0 ≤ r ∧ r < 1 ∧ Polynomial.eval ζ p = 1 ∧
        ∀ z ∈ K, ‖Polynomial.eval z p‖ ≤ r := by
  obtain ⟨a, lam, r, ha, _hlam, hr_nonneg, hr_lt, hbound⟩ :=
    exists_affine_contraction K hK hne hconvex hζ
  let p : Polynomial ℂ :=
    Polynomial.C 1 + Polynomial.C ((a : ℂ) * lam) *
      (Polynomial.X - Polynomial.C ζ)
  refine ⟨p, r, hr_nonneg, hr_lt, ?_, ?_⟩
  · simp only [p, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      sub_self, mul_zero, add_zero]
  · intro z hz
    simpa only [p, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      mul_assoc] using hbound z hz
