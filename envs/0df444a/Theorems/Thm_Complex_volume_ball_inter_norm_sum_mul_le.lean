-- Prove2me | Theorems.Thm_Complex_volume_ball_inter_norm_sum_mul_le
-- name    : Complex.volume_ball_inter_norm_sum_mul_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/3e8bfa6c-cc38-54de-a641-a93fee3724af
-- title:
--   Small-value bound for a linear form on the unit polydisc
-- statement:
--   Let $n$ be a natural number and let $w : \mathrm{Fin}\,n \to \mathbb{C}$ be a non-zero vector, where $\mathbb{C}^n = (\mathrm{Fin}\,n \to \mathbb{C})$ carries the supremum norm, so that $\|w\| = \max_j |w_j|$ and $\mathrm{ball}(0,1)$ is the open unit polydisc $\{b : |b_j| < 1 \text{ for all } j\}$, and where `volume` is the product of Lebesgue measure on each $\mathbb{C}$ factor. Then for every real number $\varepsilon$ (no positivity assumed), the set of those $b$ in the open unit polydisc for which the linear form $\sum_{j} b_j w_j$ has norm at most $\varepsilon$ has measure at most $\mathrm{ofReal}\big((\varepsilon/\|w\|)^2\big)$ times the measure of the open unit polydisc; the inequality is one of extended non-negative reals, and the factor $(\varepsilon/\|w\|)^2$ is taken with division in $\mathbb{R}$ and then pushed into $[0,\infty]$ by `ENNReal.ofReal`. Since $w \neq 0$, the quotient $\varepsilon/\|w\|$ is a genuine quotient, and the hypothesis also forces $n \geq 1$.
--
--   This is an anti-concentration ("slab") estimate: a vector drawn uniformly from the unit polydisc sends a fixed non-zero linear form into the disc of radius $\varepsilon$ with probability at most $(\varepsilon/\|w\|_\infty)^2$; it is sharp up to the constant, as $w = e_1$ shows. It is the measure-theoretic input for [`Complex.volume_ball_inter_exists_sum_mul_eq_zero_le`](thm.html#Complex.volume_ball_inter_exists_sum_mul_eq_zero_le) and, through it, for the existence of hyperplane sections with controlled defect and with controlled sums of logarithmic section values on the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_volume_ball_inter_norm_sum_mul_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Metric

theorem Complex.volume_ball_inter_norm_sum_mul_le {n : ℕ} (w : Fin n → ℂ) (hw : w ≠ 0) (ε : ℝ) :
    volume {b : Fin n → ℂ | b ∈ Metric.ball 0 1 ∧ ‖∑ j, b j * w j‖ ≤ ε}
      ≤ ENNReal.ofReal ((ε / ‖w‖) ^ 2) * volume (Metric.ball (0 : Fin n → ℂ) 1) := by sorry
