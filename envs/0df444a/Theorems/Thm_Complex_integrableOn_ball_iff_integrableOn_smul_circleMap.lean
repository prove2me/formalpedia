-- Prove2me | Theorems.Thm_Complex_integrableOn_ball_iff_integrableOn_smul_circleMap
-- name    : Complex.integrableOn_ball_iff_integrableOn_smul_circleMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/57c8041e-389a-5d7a-a8c4-b7f04401802b
-- title:
--   Integrability on a disc via polar coordinates
-- statement:
--   Let $E$ be a real normed vector space (a normed additive commutative group with a normed $\mathbb{R}$-module structure), let $f : \mathbb{C} \to E$, let $c \in \mathbb{C}$ and let $R \in \mathbb{R}$ be arbitrary (no positivity is assumed). The assertion is an equivalence: $f$ is integrable, in the Bochner sense, on the open ball $\mathrm{ball}(c,R) \subseteq \mathbb{C}$ with respect to the area measure on $\mathbb{C}$ if and only if the function $(r,\theta) \mapsto r \cdot f(\mathrm{circleMap}\,c\,r\,\theta) = r\, f(c + r e^{i\theta})$, with $r$ acting by the real scalar multiplication on $E$, is integrable on the rectangle $(0,R) \times (-\pi,\pi) \subseteq \mathbb{R} \times \mathbb{R}$ with respect to two-dimensional Lebesgue measure. Here the factor $r$ is the Jacobian of the polar-coordinate parametrisation and $(-\pi,\pi)$ is the angular window of the polar chart; for $R \le 0$ both sides hold vacuously, both domains being empty.
--
--   This is the integrability counterpart of the polar-coordinate change of variables on a disc, allowing integrability over a disc to be tested radius by radius (via Fubini–Tonelli on the rectangle). It is used for the polar-coordinate formula [`Complex.integral_ball_eq_integral_smul_intervalIntegral_circleMap`](thm.html#Complex.integral_ball_eq_integral_smul_intervalIntegral_circleMap) and for the local integrability of $\log\lVert F\rVert$ on a ball for $F$ analytic, [`AnalyticOnNhd.integrableOn_log_norm_ball`](thm.html#AnalyticOnNhd.integrableOn_log_norm_ball).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_integrableOn_ball_iff_integrableOn_smul_circleMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Complex.integrableOn_ball_iff_integrableOn_smul_circleMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ) :
    MeasureTheory.IntegrableOn f (Metric.ball c R) ↔
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (circleMap c p.1 p.2))
        (Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi) := by sorry
