-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_lemma2_third_moment
-- name    : EntropicBarrier.Universal.lemma2_third_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:43:02.73703+00:00
-- url     : https://prove2.me/theorems/268b2c6b-f57c-4357-a2d8-45890784bc80
-- title:
--   Lemma 2 — $\mathbb EX^3\le 2(\mathbb EX^2)^{3/2}$ for a real centered log-concave $X$
-- statement:
--   Let $X$ be a real log-concave and centered random variable, with density $\lambda:\mathbb R\to[0,\infty)$: $\lambda$ is log-concave, $\int_{\mathbb R}\lambda=1$ and $\int_{\mathbb R}x\lambda(x)\,dx=0$. Then
--   $$\mathbb EX^3=\int_{\mathbb R}x^3\lambda(x)\,dx\ \le\ 2\left(\int_{\mathbb R}x^2\lambda(x)\,dx\right)^{3/2}=2\left(\mathbb EX^2\right)^{3/2}.$$
--
--   The constant $2$ is sharp (approached by exponential laws), and it is exactly the constant of self-concordance (2).
--
--   **Formalization Note** Log-concavity is the published `ConvexOptimization.LogConcaveOn Set.univ`, in the power form $\lambda(x)^a\lambda(y)^b\le\lambda(ax+by)$ that permits zeros. A log-concave law on $\mathbb R$ is either a point mass or absolutely continuous; the statement covers the absolutely continuous case, and the point mass at $0$ (the only centered one) satisfies the claim trivially. A log-concave probability density has exponential tails, so $x\lambda$, $x^2\lambda$, $x^3\lambda$ are integrable and no integrability hypothesis is needed.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 7, Lemma 2 (restated and proved pp. 10-12)

import Mathlib
import Definitions.Def_LogConcaveOn

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

theorem lemma2_third_moment (dens : ℝ → ℝ)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ dens)
    (hprob : ∫ x, dens x = 1) (hcenter : ∫ x, x * dens x = 0) :
    ∫ x, x ^ 3 * dens x ≤ 2 * (∫ x, x ^ 2 * dens x) ^ ((3 : ℝ) / 2) := by sorry

end EntropicBarrier.Universal
