-- Prove2me | Theorems.Thm_Complex_exists_le_setIntegral_ball_log_norm_sum_mul
-- name    : Complex.exists_le_setIntegral_ball_log_norm_sum_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/d18100e7-584f-58fa-b111-90938750bc5b
-- title:
--   Uniform lower bound for int_Blog|a·φ| over unit covectors
-- statement:
--   Let $r$ be a natural number, $\varphi\colon\mathbb C\to\mathbb C^{r}$ a map with components $\varphi_j(z)=\varphi(z)_j$ indexed by $j\in\mathrm{Fin}\,r$, let $z_c\in\mathbb C$ and let $R,R'$ be reals with $0<R$ and $3R<R'$. Assume that each component $z\mapsto\varphi_j(z)$ is complex differentiable on the open disc $B(z_c,R')$, and assume the non-degeneracy condition that for every non-zero $a\in\mathbb C^{r}$ there is some $z\in B(z_c,R')$ with $\sum_{j}a_j\varphi_j(z)\neq 0$, i.e. no non-trivial linear combination of the components vanishes identically on $B(z_c,R')$. The conclusion asserts the existence of a single real constant $C$ such that for every $a\in\mathbb C^{r}$ of norm $\|a\|=1$ (the supremum norm on $\mathbb C^{r}$) two things hold simultaneously: the function $z\mapsto\log\bigl\|\sum_{j}a_j\varphi_j(z)\bigr\|$ is integrable on the smaller disc $B(z_c,R)$ with respect to Lebesgue (area) measure, and its integral over $B(z_c,R)$ is at least $C$. The point is that $C$ is independent of $a$.
--
--   This is the plane potential theory input of local integrability of $\log|f|$ for a holomorphic $f\not\equiv 0$ together with the sub-mean-value property of the subharmonic function $\log|f|$, made uniform over the compact set of unit covectors $a$. It is used by [`ModularCurve.JZero.exists_hyperplaneSection_defect_le`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_defect_le) to bound the defect of hyperplane sections uniformly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_exists_le_setIntegral_ball_log_norm_sum_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Metric Set

theorem Complex.exists_le_setIntegral_ball_log_norm_sum_mul {r : ℕ} {φ : ℂ → Fin r → ℂ} {z_c : ℂ} {R R' : ℝ}
    (hR : 0 < R) (hRR' : 3 * R < R') (hφ : ∀ j, DifferentiableOn ℂ (fun z ↦ φ z j) (Metric.ball z_c R'))
    (hnd : ∀ a : Fin r → ℂ, a ≠ 0 → ∃ z ∈ Metric.ball z_c R', ∑ j, a j * φ z j ≠ 0) :
    ∃ C : ℝ, ∀ a : Fin r → ℂ, ‖a‖ = 1 →
      IntegrableOn (fun z ↦ Real.log ‖∑ j, a j * φ z j‖) (Metric.ball z_c R) ∧
      C ≤ ∫ z in Metric.ball z_c R, Real.log ‖∑ j, a j * φ z j‖ := by sorry
