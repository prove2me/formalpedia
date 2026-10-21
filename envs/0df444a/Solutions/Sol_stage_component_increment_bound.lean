-- Prove2me | solution 1 for stage_component_increment_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:05:53.55078+00:00
-- url     : https://prove2.me/submissions/688adebb-4565-4b2a-bda9-b1be4d546598

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage
import Theorems.Thm_ShorNonsmooth_NonlinEq_local_residual_linear_equivalence
import Theorems.Thm_ShorNonsmooth_NonlinEq_stage_orthDir_uniform_lower_bound
import Theorems.Thm_ShorNonsmooth_NonlinEq_stage_linear_bound_and_growth
import Theorems.Thm_ShorNonsmooth_NonlinEq_residual_after_step_quadratic
import Theorems.Thm_ShorNonsmooth_NonlinEq_orthogonal_increment_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ShorNonsmooth.NonlinEq
theorem solution {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (δ L : ℝ) (hδ : 0 < δ)
    (hLip : ∀ i, ∀ x' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      ∀ x'' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
        ‖gradient (ψ i) x' - gradient (ψ i) x''‖ ≤ L * ‖x' - x''‖)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsOrthStage ψ x)
    (k j : Fin n) (hkj : k.val < j.val)
    (M S b r : ℝ) (hM : 0 ≤ M) (hS : 0 ≤ S) (hb : 0 < b) (hr : 0 ≤ r)
    (hψj : |ψ j (x j.val)| ≤ M * (S * r))
    (hdir : b ≤ ‖orthDir ψ x j‖)
    (hnormk : ‖x k.val‖ ≤ S * r) (hnormj : ‖x j.val‖ ≤ S * r)
    (hballk : x k.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (hballj : x j.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (hballj1 : x (j.val + 1) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (horthEarlier : inner ℝ (gradient (ψ k) (x k.val)) (orthDir ψ x j) = 0) :
    |ψ k (x (j.val + 1)) - ψ k (x j.val)| ≤
      max (max L 0 * (M * S / b) * (M * S / b + 2 * S)) 1 * r ^ 2 := by
  let Lp : ℝ := max L 0
  let Q : ℝ := M * S / b
  let R : ℝ := 2 * S
  let Inc : ℝ := max (Lp * Q * (Q + R)) 1
  have hIncpos : 0 < Inc := lt_of_lt_of_le zero_lt_one (le_max_right _ 1)
  have hInccoef : Lp * Q * (Q + R) ≤ Inc := le_max_left _ 1
  have hLp : 0 ≤ Lp := le_max_right L 0
  have hLle : L ≤ Lp := le_max_left L 0
  have hQ : 0 ≤ Q := div_nonneg (mul_nonneg hM hS) hb.le
  have hR : 0 ≤ R := mul_nonneg two_pos.le hS
  let φj := orthDir ψ x j
  let p := ψ j (x j.val)
  let step := x (j.val + 1) - x j.val
  have hs : step = -(p / ‖φj‖ ^ 2) • φj := by
    change x (j.val + 1) - x j.val = _
    rw [hx j, neg_smul]
    exact sub_sub_cancel_left _ _
  have hφpos : 0 < ‖φj‖ := lt_of_lt_of_le hb hdir
  have hφne : ‖φj‖ ≠ 0 := hφpos.ne'
  have hstepnorm : ‖step‖ ≤ Q * r := by
    have hstepnormeq : ‖step‖ = |p| / ‖φj‖ := by
      rw [hs, norm_smul, Real.norm_eq_abs, abs_neg, abs_div, abs_of_pos (pow_pos hφpos 2)]
      field_simp [hφne]
    rw [hstepnormeq]
    calc
      |p| / ‖φj‖ ≤ |p| / b := div_le_div_of_nonneg_left (abs_nonneg _) hb hdir
      _ ≤ (M * (S * r)) / b := div_le_div_of_nonneg_right hψj hb.le
      _ = Q * r := by dsimp [Q]; field_simp [hb.ne']
  have hdist : ‖x k.val - x j.val‖ ≤ R * r := by
    calc
      ‖x k.val - x j.val‖ ≤ ‖x k.val‖ + ‖x j.val‖ := norm_sub_le _ _
      _ ≤ S * r + S * r := add_le_add hnormk hnormj
      _ = R * r := by dsimp [R]; ring
  by_cases hzero : step = 0
  · have hxeq : x (j.val + 1) = x j.val := sub_eq_zero.mp hzero
    rw [hxeq]
    simp only [sub_self, abs_zero]
    positivity
  · have hsteppos : 0 < ‖step‖ := norm_pos_iff.mpr hzero
    let ξ : EuclideanSpace ℝ (Fin n) := ‖step‖⁻¹ • step
    have hξnorm : ‖ξ‖ = 1 := by
      dsimp [ξ]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hsteppos]
      exact inv_mul_cancel₀ hsteppos.ne'
    have hadd : x j.val + ‖step‖ • ξ = x (j.val + 1) := by
      dsimp [ξ]
      rw [smul_smul, mul_inv_cancel₀ hsteppos.ne', one_smul]
      dsimp [step]
      abel
    have hsteporth : inner ℝ (gradient (ψ k) (x k.val)) step = 0 := by
      rw [hs, inner_smul_right, horthEarlier, mul_zero]
    have hinnerξ : inner ℝ (gradient (ψ k) (x k.val)) ξ = 0 := by
      dsimp [ξ]
      rw [inner_smul_right, hsteporth, mul_zero]
    have hinc := orthogonal_increment_bound ψ hψ δ L hδ hLip k
      (x k.val) (x j.val) ξ hξnorm (by simpa using hinnerξ) ‖step‖ hsteppos
      hballk hballj (by simpa [hadd] using hballj1)
    have hrhs : L * ‖step‖ * (‖step‖ + ‖x k.val - x j.val‖) ≤
        Lp * Q * (Q + R) * r ^ 2 := by
      have hsum : ‖step‖ + ‖x k.val - x j.val‖ ≤ (Q + R) * r := by
        linarith [hstepnorm, hdist]
      have hprod : ‖step‖ * (‖step‖ + ‖x k.val - x j.val‖) ≤
          (Q * r) * ((Q + R) * r) :=
        mul_le_mul hstepnorm hsum (add_nonneg (norm_nonneg _) (norm_nonneg _))
          (mul_nonneg hQ hr)
      calc
        L * ‖step‖ * (‖step‖ + ‖x k.val - x j.val‖)
            ≤ Lp * (‖step‖ * (‖step‖ + ‖x k.val - x j.val‖)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right hLle
            (mul_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
        _ ≤ Lp * ((Q * r) * ((Q + R) * r)) := mul_le_mul_of_nonneg_left hprod hLp
        _ = Lp * Q * (Q + R) * r ^ 2 := by ring
    calc
      |ψ k (x (j.val + 1)) - ψ k (x j.val)|
          ≤ L * ‖step‖ * (‖step‖ + ‖x k.val - x j.val‖) := by simpa [hadd] using hinc
      _ ≤ Lp * Q * (Q + R) * r ^ 2 := hrhs
      _ ≤ Inc * r ^ 2 := mul_le_mul_of_nonneg_right hInccoef (sq_nonneg r)
      _ = max (max L 0 * (M * S / b) * (M * S / b + 2 * S)) 1 * r ^ 2 := rfl
