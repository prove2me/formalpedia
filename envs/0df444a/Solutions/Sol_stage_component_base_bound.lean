-- Prove2me | solution 1 for stage_component_base_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T15:48:56.810365+00:00
-- url     : https://prove2.me/submissions/0fb0ff93-01a9-49db-8a21-fd70e3cc0376

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
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsOrthStage ψ x) (k : Fin n)
    (M S b r : ℝ) (hM : 0 ≤ M) (hS : 0 ≤ S) (hb : 0 < b) (hr : 0 ≤ r)
    (hψk : |ψ k (x k.val)| ≤ M * (S * r))
    (hdir : b ≤ ‖orthDir ψ x k‖)
    (hxk : x k.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (hxk1 : x (k.val + 1) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) :
    |ψ k (x (k.val + 1))| ≤ max (max L 0 * (M * S) ^ 2 / (b / 2) ^ 2) 1 * r ^ 2 := by
  let Base : ℝ := max (max L 0 * (M * S) ^ 2 / (b / 2) ^ 2) 1
  have hbasecoef : max L 0 * (M * S) ^ 2 / (b / 2) ^ 2 ≤ Base := le_max_left _ 1
  have hLp : 0 ≤ max L 0 := le_max_right L 0
  have hLle : L ≤ max L 0 := le_max_left L 0
  have hφ : b / 2 < ‖orthDir ψ x k‖ := lt_of_lt_of_le (half_lt_self hb) hdir
  have hq := residual_after_step_quadratic ψ hψ δ L hδ hLip x hx k hxk hxk1
    (b / 2) (half_pos hb) hφ
  have hsquare : ψ k (x k.val) ^ 2 ≤ (M * (S * r)) ^ 2 := by
    nlinarith [abs_nonneg (ψ k (x k.val)), sq_abs (ψ k (x k.val)), hψk]
  calc
    |ψ k (x (k.val + 1))| ≤ L * ψ k (x k.val) ^ 2 / ‖orthDir ψ x k‖ ^ 2 := hq.1
    _ ≤ L / (b / 2) ^ 2 * ψ k (x k.val) ^ 2 := hq.2
    _ ≤ max L 0 / (b / 2) ^ 2 * ψ k (x k.val) ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hLle (sq_nonneg _)) (sq_nonneg _)
    _ ≤ max L 0 / (b / 2) ^ 2 * (M * (S * r)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (div_nonneg hLp (sq_nonneg _))
    _ = (max L 0 * (M * S) ^ 2 / (b / 2) ^ 2) * r ^ 2 := by ring
    _ ≤ Base * r ^ 2 := mul_le_mul_of_nonneg_right hbasecoef (sq_nonneg r)
    _ = max (max L 0 * (M * S) ^ 2 / (b / 2) ^ 2) 1 * r ^ 2 := rfl
