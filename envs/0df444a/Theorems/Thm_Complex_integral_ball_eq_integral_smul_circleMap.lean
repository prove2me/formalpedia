-- Prove2me | Theorems.Thm_Complex_integral_ball_eq_integral_smul_circleMap
-- name    : Complex.integral_ball_eq_integral_smul_circleMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/2300ec30-5256-5022-b2a8-b6d80f05d36c
-- title:
--   Polar coordinates on a disc
-- statement:
--   Let $E$ be a real normed vector space (a normed additive commutative group with a real normed space structure), let $f : \mathbb{C} \to E$ be an arbitrary function, let $c \in \mathbb{C}$ and let $R \in \mathbb{R}$ be arbitrary. The assertion is the equality of two Bochner integrals: the integral of $f$ over the open ball $\{z : |z - c| < R\}$ in $\mathbb{C}$, taken with respect to Lebesgue (area) measure restricted to that ball, equals the integral over the rectangle $(0,R) \times (-\pi,\pi) \subseteq \mathbb{R} \times \mathbb{R}$, with respect to two-dimensional Lebesgue measure restricted to that rectangle, of the function $p \mapsto p_1 \cdot f(\mathrm{circleMap}\ c\ p_1\ p_2)$, where $\mathrm{circleMap}\ c\ r\ \theta = c + r e^{i\theta}$ and the scalar $p_1$ acts on $E$ by the real scalar multiplication. No continuity, measurability or integrability hypothesis is imposed on $f$, and no sign condition on $R$: since both sides are Bochner integrals, which vanish when the integrand fails to be integrable, the two sides are equal unconditionally (for $R \le 0$ both the ball and the rectangle are empty and both sides are $0$).
--
--   This is the change of variables to polar coordinates centred at an arbitrary point and cut off to a disc, Mathlib providing only the whole-plane version. It serves to convert integrals over circles $|z-c| = r$ into area integrals over discs, and is used by the companion statement [`Complex.integral_ball_eq_integral_smul_intervalIntegral_circleMap`](thm.html#Complex.integral_ball_eq_integral_smul_intervalIntegral_circleMap), which rewrites the right-hand side as an iterated interval integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_integral_ball_eq_integral_smul_circleMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Complex.integral_ball_eq_integral_smul_circleMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ) :
    ∫ z in Metric.ball c R, f z
      = ∫ p in Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, p.1 • f (circleMap c p.1 p.2) := by sorry
