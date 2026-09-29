-- Prove2me | Theorems.Thm_AnalyticOnNhd_log_norm_sub_mul_le_setAverage_ball
-- name    : AnalyticOnNhd.log_norm_sub_mul_le_setAverage_ball
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/e45e0374-4338-5a17-a3f3-168b294c5b2a
-- title:
--   Solid sub-mean-value inequality for log‖F‖-kg on a disc
-- statement:
--   Let $F:\mathbb{C}\to\mathbb{C}$, $g:\mathbb{C}\to\mathbb{R}$, $c\in\mathbb{C}$ and real numbers $R,k,M$ be given. Assume that $F$ is analytic on a neighbourhood of each point of the closed disc $\overline{D}(c,R)$, that $F(c)\neq 0$, that $R>0$, that $g$ is continuous on $\overline{D}(c,R)$, that $g(z)\le M$ for every $z\in\overline{D}(c,R)$, and that $k\ge 0$. Then $$\log\|F(c)\|-kM\;\le\;\frac{1}{\pi R^2}\int_{D(c,R)}\bigl(\log\|F(z)\|-k\,g(z)\bigr)\,dA,$$ the right-hand side being the Mathlib set average of the function $z\mapsto\log\|F(z)\|-k\,g(z)$ over the open disc $D(c,R)$ with respect to Lebesgue measure on $\mathbb{C}$, i.e. $(\pi R^2)^{-1}\int_{D(c,R)}(\log\|F\|-kg)\,dA$. Here $\log$ is the real logarithm with the convention $\log 0 = 0$, so the hypothesis $F(c)\neq 0$ is what makes the left-hand side meaningful; and $R>0$ is needed because the average over a null or empty set vanishes by convention.
--
--   This is the solid (area) form of the sub-mean-value property of the weighted quantity $\log\|F\|-kg$: the value at the centre of a disc is dominated by the disc average, up to the defect $k(M-g)$ caused by the weight; for $k=0$ it reduces to $\log\|F(c)\|\le(\pi R^2)^{-1}\int_{D(c,R)}\log\|F\|\,dA$. It feeds the selection arguments [`Complex.exists_le_setIntegral_ball_log_norm_sum_mul`](thm.html#Complex.exists_le_setIntegral_ball_log_norm_sum_mul) and [`ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge), where a point with a lower bound on a sum of logarithms of analytic functions is produced from an average over a disc.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AnalyticOnNhd_log_norm_sub_mul_le_setAverage_ball.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AnalyticOnNhd.log_norm_sub_mul_le_setAverage_ball {F : ℂ → ℂ} {g : ℂ → ℝ} {c : ℂ}
    {R k M : ℝ} (hF : AnalyticOnNhd ℂ F (Metric.closedBall c R)) (hc : F c ≠ 0) (hR : 0 < R)
    (hg : ContinuousOn g (Metric.closedBall c R)) (hM : ∀ z ∈ Metric.closedBall c R, g z ≤ M)
    (hk : 0 ≤ k) :
    Real.log ‖F c‖ - k * M ≤ ⨍ z in Metric.ball c R, (Real.log ‖F z‖ - k * g z) := by sorry
