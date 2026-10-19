-- Prove2me | Theorems.Thm_ContWeatherall_contDiff_parametric_intervalIntegral
-- name    : ContWeatherall.contDiff_parametric_intervalIntegral
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-18T21:05:06.609894+00:00
-- url     : https://prove2.me/theorems/0f4cf00c-7ff4-4cf1-8753-27a70dddbf08
-- title:
--   Smooth parametric interval integrals are smooth
-- statement:
--   Let $H$ be a real normed space and $G$ a real Banach space, and let $f : H\times\mathbb R\to G$, $(x,t)\mapsto f(x,t)$, be jointly $C^\infty$. Then for all $a,b\in\mathbb R$ the parametric integral
--   $$x\;\longmapsto\;\int_a^b f(x,t)\,dt$$
--   is a $C^\infty$ map $H\to G$. (Here $\int_a^b$ is the oriented interval integral, so $\int_a^b=-\int_b^a$.)
--
--   *Proof idea.* By induction on the order $n$, for all Banach targets at once. Order $0$ is continuity of parametric integrals. For order $n+1$, differentiate under the integral sign. On the compact set $\{x_0\}\times[a,b]$, the partial derivative $D_xf$ is bounded by some $C$. A tube-lemma argument then bounds it by $C+1$ on $U\times[a,b]$ for a neighbourhood $U$ of $x_0$. Dominated convergence gives $D\!\left(\int_a^b f(\cdot,t)\,dt\right)(x)=\int_a^b D_xf(x,t)\,dt$, and $D_xf$ is again jointly $C^\infty$, now with values in the Banach space $L(H,G)$. Note that $H$ need not be finite-dimensional or complete.
-- source:
--   Standard differentiation under the integral sign; cf. J. Dieudonné, Foundations of Modern Analysis (1960), (8.11.2); used in M. Spivak, Calculus on Manifolds (1965), proof of Theorem 4-11

import Mathlib

open scoped ContDiff

namespace ContWeatherall

/-- Smoothness under the integral sign: if `(x, t) ↦ f x t` is jointly `C^∞`, then
`x ↦ ∫ t in a..b, f x t` is `C^∞`. -/
theorem contDiff_parametric_intervalIntegral {H G : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : H → ℝ → G} (hf : ContDiff ℝ ∞ (Function.uncurry f)) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..b, f x t) := by
  sorry

end ContWeatherall
