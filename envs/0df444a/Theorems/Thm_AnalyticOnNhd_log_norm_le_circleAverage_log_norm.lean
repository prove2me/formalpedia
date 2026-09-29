-- Prove2me | Theorems.Thm_AnalyticOnNhd_log_norm_le_circleAverage_log_norm
-- name    : AnalyticOnNhd.log_norm_le_circleAverage_log_norm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/bf4f6546-9398-53e2-8732-63551bb3ba92
-- title:
--   Sub-mean-value inequality for log‖F‖ on circles
-- statement:
--   Let $F:\mathbb{C}\to\mathbb{C}$, let $c\in\mathbb{C}$ and let $R\in\mathbb{R}$ be arbitrary (no sign or nonvanishing condition on $R$ is imposed). Assume that $F$ is analytic on a neighbourhood of every point of the closed disc $\overline{D}(c,|R|)=\{z:\ |z-c|\le |R|\}$, i.e. `AnalyticOnNhd ℂ F (Metric.closedBall c |R|)`, and that $F(c)\neq 0$. The conclusion is the inequality $$\log\|F(c)\|\ \le\ \frac{1}{2\pi}\int_{0}^{2\pi}\log\bigl\|F(c+Re^{i\theta})\bigr\|\,\mathrm{d}\theta,$$ the right-hand side being Mathlib's `Real.circleAverage` of the function $z\mapsto\log\|F(z)\|$ over the circle of centre $c$ and (signed) radius $R$; note that the circle traversed by $R$ and by $-R$ is the same, and that for $R=0$ the circle average degenerates to $\log\|F(c)\|$, so both sides agree. Here $\log$ is the real logarithm with the convention $\log 0 = 0$, which is harmless at $c$ by the hypothesis $F(c)\neq 0$ but is in force at any zeros of $F$ lying on the circle.
--
--   This is the elementary form of the sub-mean-value (subharmonicity) property of $\log\|F\|$ for $F$ holomorphic, obtained from Jensen's formula by discarding the non-negative contribution of the zeros in the open disc. It serves as the basic inequality for estimates of $\log\|F\|$ on discs, and is used here in the proofs of [`AnalyticOnNhd.integrableOn_log_norm_ball`](thm.html#AnalyticOnNhd.integrableOn_log_norm_ball) and [`AnalyticOnNhd.log_norm_sub_mul_le_circleAverage`](thm.html#AnalyticOnNhd.log_norm_sub_mul_le_circleAverage).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AnalyticOnNhd_log_norm_le_circleAverage_log_norm.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AnalyticOnNhd.log_norm_le_circleAverage_log_norm {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c |R|)) (hc : F c ≠ 0) :
    Real.log ‖F c‖ ≤ Real.circleAverage (fun z ↦ Real.log ‖F z‖) c R := by sorry
