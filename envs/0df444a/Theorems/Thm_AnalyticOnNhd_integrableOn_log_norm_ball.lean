-- Prove2me | Theorems.Thm_AnalyticOnNhd_integrableOn_log_norm_ball
-- name    : AnalyticOnNhd.integrableOn_log_norm_ball
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/dc72c1f0-7e02-55de-80c3-c416d77350ea
-- title:
--   Integrability of log‖F‖ on a disc
-- statement:
--   Let $F:\mathbb{C}\to\mathbb{C}$, let $c\in\mathbb{C}$ and let $R\in\mathbb{R}$ be arbitrary (no positivity is assumed; for $R\le 0$ the open ball is empty). Assume that $F$ is analytic on a neighbourhood of every point of the closed ball $\overline{B}(c,R)=\{z:|z-c|\le R\}$, in the sense of `AnalyticOnNhd ℂ F (Metric.closedBall c R)`, and that $F(c)\neq 0$. The conclusion is that the real-valued function $z\mapsto \log\|F(z)\|$ is integrable on the open ball $B(c,R)$ with respect to the Lebesgue (area) measure on $\mathbb{C}$, i.e. it is almost everywhere strongly measurable there and $\int_{B(c,R)}\bigl|\log\|F(z)\|\bigr|\,dA(z)<\infty$. Here $\log$ is the real logarithm with the convention $\log 0 = 0$, so no separate convention is needed at the zeros of $F$. The hypothesis $F(c)\neq 0$ is a sufficient condition tailored to the proof, which passes through the value of $\log\|F\|$ at the centre; the classical statement for arbitrary $F\not\equiv 0$ on a connected neighbourhood is not asserted.
--
--   This is the local integrability of $\log\|F\|$ for a holomorphic $F$ not vanishing at the centre, the basic fact making area averages of $\log\|F\|$ meaningful (it reflects the subharmonicity of $\log\|F\|$). It is used by [`AnalyticOnNhd.log_norm_sub_mul_le_setAverage_ball`](thm.html#AnalyticOnNhd.log_norm_sub_mul_le_setAverage_ball), [`Complex.exists_le_setIntegral_ball_log_norm_sum_mul`](thm.html#Complex.exists_le_setIntegral_ball_log_norm_sum_mul) and [`ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AnalyticOnNhd_integrableOn_log_norm_ball.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AnalyticOnNhd.integrableOn_log_norm_ball {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c R)) (hc : F c ≠ 0) :
    MeasureTheory.IntegrableOn (fun z ↦ Real.log ‖F z‖) (Metric.ball c R) := by sorry
