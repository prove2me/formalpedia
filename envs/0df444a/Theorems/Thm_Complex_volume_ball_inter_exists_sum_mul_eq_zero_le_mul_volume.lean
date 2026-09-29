-- Prove2me | Theorems.Thm_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume
-- name    : Complex.volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/17314f9f-1d3f-5195-bd87-e0b2629a78e7
-- title:
--   Crofton-type bound for random hyperplanes meeting c(S)
-- statement:
--   Let $n$ be a natural number, let $c : \mathbb{C} \to (\mathrm{Fin}\ n \to \mathbb{C})$ be an arbitrary map (no continuity or measurability assumed), let $S \subseteq \mathbb{C}$ be an arbitrary set, and let $\eta, L$ be real numbers with $0 < \eta$. Assume: (i) $\eta \le \|c(z)\|$ for every $z \in S$, the norm on $\mathrm{Fin}\ n \to \mathbb{C}$ being the supremum norm; (ii) for every $z \in S$ there is $\delta > 0$ such that $\|c(y) - c(z)\| \le L\,|y - z|$ for all $y$ in the closed disc of radius $\delta$ about $z$, i.e. $c$ is $L$-Lipschitz at $z$ on some disc about $z$. Then, with `volume` the Lebesgue measure on $\mathrm{Fin}\ n \to \mathbb{C}$ in the first and third factor sense (product Lebesgue measure on $\mathbb{C}^n$, and plane Lebesgue outer measure on $\mathbb{C}$ for $S$),
--   $$\mathrm{vol}\Bigl\{\,b \in \mathbb{C}^n : \|b\| < 1 \text{ and } \exists z \in S,\ \sum_{j} b_j\,c_j(z) = 0 \Bigr\} \le \mathrm{ofReal}\Bigl(\tfrac{(nL/\eta)^2}{\pi}\Bigr)\cdot \mathrm{vol}\bigl(B(0,1)\bigr)\cdot \mathrm{vol}(S),$$
--   where $B(0,1)$ is the open unit ball of the sup norm, i.e. the open unit polydisc, and the inequality is one of extended nonnegative reals.
--
--   This is a Crofton-type estimate: for $b$ uniform in the unit polydisc, the probability that the hyperplane $\sum_j b_j x_j = 0$ meets the image $c(S)$ is at most $\pi^{-1}(nL/\eta)^2\,\mathrm{area}(S)$, valid for an arbitrary (not necessarily measurable) $S$ on which $c$ is bounded away from $0$ and locally $L$-Lipschitz. It is used in the construction of hyperplane sections of modular curves with controlled defect, through [`ModularCurve.JZero.exists_hyperplaneSection_defect_le`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_defect_le) and [`ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Metric
open scoped ENNReal NNReal

theorem Complex.volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume {n : ℕ} (c : ℂ → Fin n → ℂ)
    (S : Set ℂ) {η L : ℝ} (hη : 0 < η) (hηc : ∀ z ∈ S, η ≤ ‖c z‖)
    (hLip : ∀ z ∈ S, ∃ δ > 0, ∀ y ∈ Metric.closedBall z δ, ‖c y - c z‖ ≤ L * ‖y - z‖) :
    volume {b : Fin n → ℂ | b ∈ Metric.ball 0 1 ∧ ∃ z ∈ S, ∑ j, b j * c z j = 0}
      ≤ ENNReal.ofReal ((n * L / η) ^ 2 / Real.pi) * volume (Metric.ball (0 : Fin n → ℂ) 1) * volume S := by sorry
