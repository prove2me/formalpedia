-- Prove2me | Theorems.Thm_AnalyticOnNhd_log_norm_sub_mul_le_circleAverage
-- name    : AnalyticOnNhd.log_norm_sub_mul_le_circleAverage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/86ab4c25-646a-579d-b810-6b6cda80978a
-- title:
--   Weighted sub-mean-value inequality for log‖F‖
-- statement:
--   Let $F:\mathbb{C}\to\mathbb{C}$, let $c\in\mathbb{C}$ and let $R$ be a real number. Assume $F$ is analytic on a neighbourhood of each point of the closed ball $\overline{B}(c,|R|)$, and $F(c)\neq 0$. Let $g:\mathbb{C}\to\mathbb{R}$ be circle-integrable with centre $c$ and radius $R$, i.e. $\theta\mapsto g(c+Re^{i\theta})$ is interval-integrable over $[0,2\pi]$, and let $k,M$ be reals with $g(z)\le M$ for every $z$ on the sphere of centre $c$ and radius $|R|$, and $0\le k$. Then $$\log\|F(c)\|-kM\;\le\;\frac{1}{2\pi}\int_0^{2\pi}\Bigl(\log\bigl\|F(c+Re^{i\theta})\bigr\|-k\,g\bigl(c+Re^{i\theta}\bigr)\Bigr)\,d\theta,$$ the right-hand side being the normalised circle average `Real.circleAverage` of $z\mapsto \log\|F(z)\|-k\,g(z)$ over the circle of centre $c$ and radius $R$. Note that the bound $M$ is imposed only on the circle $\|z-c\|=|R|$, and that the radius $R$ is an arbitrary real number, with the analyticity and the bound formulated on the set of radius $|R|$.
--
--   This is the sub-mean-value property of $\log\|F\|$ in weighted form: the circle average of the quasi-subharmonic function $\log\|F\|-k\,g$ dominates its value at the centre up to the defect $k(M-g(c))$, which depends on the weight alone. It is used to derive the corresponding inequality for averages over the solid ball, [`AnalyticOnNhd.log_norm_sub_mul_le_setAverage_ball`](thm.html#AnalyticOnNhd.log_norm_sub_mul_le_setAverage_ball).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AnalyticOnNhd_log_norm_sub_mul_le_circleAverage.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AnalyticOnNhd.log_norm_sub_mul_le_circleAverage {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c |R|)) (hc : F c ≠ 0) {g : ℂ → ℝ} {k M : ℝ}
    (hg : CircleIntegrable g c R) (hM : ∀ z ∈ Metric.sphere c |R|, g z ≤ M) (hk : 0 ≤ k) :
    Real.log ‖F c‖ - k * M ≤ Real.circleAverage (fun z ↦ Real.log ‖F z‖ - k * g z) c R := by sorry
