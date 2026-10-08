-- Prove2me | Theorems.Thm_AdaptiveCubic_Cauchy_lemma_3_1_i
-- name    : AdaptiveCubic.Cauchy.lemma_3_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:50.715032+00:00
-- url     : https://prove2.me/theorems/ed9223c1-2049-401b-9ecf-b077307b849d
-- title:
--   Lemma 3.1 i) (3.3) — Cauchy decrease of the cubic model
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, $x\in\mathbb R^n$ with gradient $g=\nabla f(x)$, $B$ a symmetric matrix and $\sigma>0$, and let $m$ be the cubic model at $x$ with these data. If the step $s$ satisfies the Cauchy condition (2.2), i.e. $m(s)\le m(-\alpha g)$ for every $\alpha\ge0$, then
--
--   $$
--   f(x)-m(s)\ge\frac{\|g\|}{6\sqrt2}\,\min\left[\frac{\|g\|}{1+\|B\|},\ \frac12\sqrt{\frac{\|g\|}{\sigma}}\right],
--   $$
--
--   where $\|B\|$ is the operator norm induced by the Euclidean norm.
--
--   This is the basic model decrease guaranteed by the Cauchy point; in particular $m(s)<f(x)$ whenever $g\neq0$, which is (2.7). The result is quoted from Part I of the paper (Lemma 2.1 there).
--
--   **Formalization Note** The statement concerns one iteration, so the index $k$ is dropped. At $g=0$ the left-hand side is $0$ and the inequality reads $0\le f(x)-m(s)$; it is not excluded. $B$ is a continuous linear operator on `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 7, Lemma 3.1 i), (3.3)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.Cauchy

/-- Lemma 3.1 i), (3.3), p. 7 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009;
quoted from Part I, Lemma 2.1). For one iteration with iterate `x`, symmetric `B`, weight `σ > 0`
and a step `s` satisfying the Cauchy condition (2.2) (`m(s) ≤ m(−α g)` for all `α ≥ 0`):
`f(x) − m(s) ≥ (‖g‖ / (6√2)) · min(‖g‖ / (1 + ‖B‖), ½ √(‖g‖/σ))`, with `g = ∇f(x)`. -/
theorem lemma_3_1_i {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hB : IsSelfAdjoint B)
    (σ : ℝ) (hσ : 0 < σ) (x s : EuclideanSpace ℝ (Fin n))
    (hcauchy : ∀ α : ℝ, 0 ≤ α → model f B σ x s ≤ model f B σ x (-(α • gradient f x))) :
    ‖gradient f x‖ / (6 * √2) *
        min (‖gradient f x‖ / (1 + ‖B‖)) (1 / 2 * √(‖gradient f x‖ / σ)) ≤
      f x - model f B σ x s := by sorry

end AdaptiveCubic.Cauchy
