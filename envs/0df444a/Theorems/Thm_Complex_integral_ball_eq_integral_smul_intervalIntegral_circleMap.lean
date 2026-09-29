-- Prove2me | Theorems.Thm_Complex_integral_ball_eq_integral_smul_intervalIntegral_circleMap
-- name    : Complex.integral_ball_eq_integral_smul_intervalIntegral_circleMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/92d2bf8c-6ab9-5271-b682-2977a9e3dbdc
-- title:
--   Polar coordinates on a disc, iterated form
-- statement:
--   Let $E$ be a real normed vector space (a normed additive commutative group with a normed $\mathbb{R}$-module structure), let $f : \mathbb{C} \to E$, let $c \in \mathbb{C}$ and let $R \in \mathbb{R}$, with no sign restriction on $R$. Assume $f$ is integrable on the open ball $B(c,R)$ of $\mathbb{C}$ with respect to the restriction of Lebesgue (area) measure. Then the Bochner integral of $f$ over $B(c,R)$ equals the integral, over $r$ ranging in the open interval $(0,R)$, of the scalar multiple by $r$ of the interval integral $\int_0^{2\pi} f(\mathrm{circleMap}\ c\ r\ \theta)\,\mathrm{d}\theta$, where $\mathrm{circleMap}\ c\ r\ \theta = c + r e^{i\theta}$. In symbols, $\int_{B(c,R)} f(z)\,\mathrm{d}z = \int_{(0,R)} r \cdot \bigl(\int_0^{2\pi} f(c + re^{i\theta})\,\mathrm{d}\theta\bigr)\,\mathrm{d}r$. The outer integral is a set integral over `Set.Ioo 0 R`, so for $R \le 0$ both sides vanish; the inner integral is an interval integral over the window $[0,2\pi]$ rather than $[-\pi,\pi]$.
--
--   This is the Fubini, or iterated, form of the polar-coordinate change of variables on a disc: the area integral is the integral over radii of $r$ times the integral of $f$ over the circle of radius $r$ about $c$. It is the form used to pass between area averages over a disc and circle averages, and it is invoked in the proof of the sub-mean-value inequality [`AnalyticOnNhd.log_norm_sub_mul_le_setAverage_ball`](thm.html#AnalyticOnNhd.log_norm_sub_mul_le_setAverage_ball) for $\log\|F\|$ with $F$ analytic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_integral_ball_eq_integral_smul_intervalIntegral_circleMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Complex.integral_ball_eq_integral_smul_intervalIntegral_circleMap {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : MeasureTheory.IntegrableOn f (Metric.ball c R)) :
    ∫ z in Metric.ball c R, f z = ∫ r in Set.Ioo 0 R, r • ∫ θ in 0..2 * Real.pi, f (circleMap c r θ) := by sorry
