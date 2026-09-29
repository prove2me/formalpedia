-- Prove2me | Theorems.Thm_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le
-- name    : Complex.volume_ball_inter_exists_sum_mul_eq_zero_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/eefc5e49-65b6-512e-885d-315a1263e3aa
-- title:
--   Rare vanishing of a random linear form along a small arc
-- statement:
--   Let $n$ be a natural number, let $c:\mathbb{C}\to(\mathrm{Fin}\,n\to\mathbb{C})$ be an arbitrary map (no continuity assumed), let $z_0\in\mathbb{C}$, and let $K\subseteq\mathbb{C}$ be an arbitrary set. Assume $c(z_0)\neq 0$ and that for some real $\delta$ one has $\|c(z)-c(z_0)\|\le\delta$ for every $z\in K$, the norm being the sup norm on $\mathrm{Fin}\,n\to\mathbb{C}$. Then the Lebesgue (product) measure of the set of those $b\in\mathrm{Fin}\,n\to\mathbb{C}$ which lie in the open unit ball $\mathrm{ball}(0,1)$ for the sup norm — that is, the open unit polydisc — and for which there exists $z\in K$ with $\sum_{j} b_j\,c(z)_j=0$, is at most $$\mathrm{ofReal}\Bigl(\bigl(n\delta/\|c(z_0)\|\bigr)^{2}\Bigr)\cdot\mathrm{volume}\bigl(\mathrm{ball}(0,1)\bigr),$$ the scalar being coerced to $\overline{\mathbb{R}}_{\ge0}$ via `ENNReal.ofReal`. Since `volume` is an outer measure, no measurability of the set (which involves an existential quantifier over the arbitrary set $K$) is needed.
--
--   This is a moving-target form of the polydisc slab estimate: for $b$ uniform in the unit polydisc, the hyperplane $\{x:\sum_j b_jx_j=0\}$ meets the piece $c(K)$ of a curve with probability $O((\operatorname{osc}_K c/\|c(z_0)\|)^2)$. It is used in the choice of a hyperplane section avoiding prescribed small arcs, feeding [`Complex.volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume`](thm.html#Complex.volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume) and [`ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Metric

theorem Complex.volume_ball_inter_exists_sum_mul_eq_zero_le {n : ℕ} (c : ℂ → Fin n → ℂ) (z₀ : ℂ) (K : Set ℂ)
    (hc : c z₀ ≠ 0) {δ : ℝ} (hδ : ∀ z ∈ K, ‖c z - c z₀‖ ≤ δ) :
    volume {b : Fin n → ℂ | b ∈ Metric.ball 0 1 ∧ ∃ z ∈ K, ∑ j, b j * c z j = 0}
      ≤ ENNReal.ofReal ((n * δ / ‖c z₀‖) ^ 2) * volume (Metric.ball (0 : Fin n → ℂ) 1) := by sorry
