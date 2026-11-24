-- Prove2me | Theorems.Thm_AccelMM_BTMap_Supplement_theorem_7_1
-- name    : AccelMM.BTMap.Supplement.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:17:17.304219+00:00
-- url     : https://prove2.me/theorems/309167f6-9358-41d0-beb4-467b287a1115
-- title:
--   Theorem 7.1 (companion theorem; not used in the proof of the goal) (corrected: segment [x*, x] in 𝒳_µ) — first-order-surrogate MM rate
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ and $\mu_0,\gamma>0$. Let $\mathcal X_\gamma$ be a convex set on which $f$ is differentiable and $\gamma$-strongly convex, $f(u)-f(v)\le\nabla f(u)^\top(u-v)-\tfrac\gamma2\|u-v\|^2$ for $u,v\in\mathcal X_\gamma$, and let $x^*\in\mathcal X_\gamma$ be a global minimizer of $f$. Let $g(u;v)$ be a majorant surrogate of $f$ ($f(u)\le g(u;v)$ and $g(u;u)=f(u)$ for all $u,v$) that is a first-order surrogate on $\mathcal X_\mu$ with parameter $\mu_0$: for every base point $y\in\mathcal X_\mu$ the error $h(\cdot\,;y)=g(\cdot\,;y)-f$ is differentiable on $\mathcal X_\mu$ with $\mu_0$-Lipschitz gradient there. Let $x\in\mathcal X_\gamma$ and let $x^+$ be any global minimizer of $g(\cdot\,;x)$, with $x^+\in\mathcal X_\mu$. If the segment $[x^*,x]$ lies in $\mathcal X_\mu$, then
--   $$f(x^+)-f(x^*)\le c\,\bigl(f(x)-f(x^*)\bigr),\qquad c=\begin{cases}\mu_0/\gamma,&\gamma>2\mu_0,\\ 1-\gamma/(4\mu_0),&\gamma\le2\mu_0.\end{cases}$$
--   This is the paper's restatement of Mairal's (2015) MM rate, compared in §7.3 with Theorem 3.2.
--
--   **Formalization Note** The paper does not define "first-order surrogate on $\mathcal X_\mu$"; the reading above is the one §7.6 (p. 21) verifies for the Bradley–Terry surrogate. As printed, Theorem 7.1 is false under it, even when $x\in\mathcal X_\mu$: nothing relates $\mathcal X_\gamma$ to $\mathcal X_\mu$, while the proof (p. 19) applies the first-order bound at the points $ax^*+(1-a)x$. The premise $[x^*,x]\subseteq\mathcal X_\mu$ is added; it follows from the inclusion $\mathcal X_\gamma\subseteq\mathcal X_\mu$ of Theorems 3.1–3.2 and excludes only steps whose segment leaves $\mathcal X_\mu$. The counterexample is in the mission's disproof record.
--
--   Differences from the source:
--   - encoding: vectors in ℝⁿ and a step at time t → EuclideanSpace ℝ (Fin n) and arbitrary current and next points; the MM output is any global minimizer of g(·; x^(t)) (hstep); reason: Fin n indexes coordinates from zero; the MM algorithm (2.6) takes an argmin, expressed relationally without a choice function
--   - reading: f is a strongly convex function on 𝒳_γ (with the γ of the rate c) → Convex ℝ Xγ, StronglyConvexOn f Xγ γ (the paper's subgradient form, p. 7), true differentiability of f on Xγ, 0 < γ; reason: the rate c involves γ, so γ is the strong-convexity modulus; the definition on p. 7 uses ∇f, and the proof's 'by convexity of f' on the segment [x*, x^(t)] uses a convex domain
--   - reading: g is a first-order surrogate function of f on 𝒳_µ with parameter µ₀ > 0 → IsMajorant g f, and for every base point y ∈ Xμ the error v ↦ g(v; y) − f(v) is differentiable at every point of Xμ and µ₀-smooth on Xμ (SmoothOn), with 0 < μ₀; reason: the paper does not define the notion (it cites Mairal (2015)); §7.6, p. 21 verifies it for (2.7) exactly as 'the error function h(x; y) = ℓ(x) − ℓ(x; y) is a µ₀-smooth function on 𝒳_ω'; the MM algorithm (2.6) is defined for majorant surrogates, which makes h ≥ 0 with h(y; y) = 0
--   - encoding: c = µ₀/γ if γ > 2µ₀; 1 − γ/(4µ₀) if γ ≤ 2µ₀ → if 2 * μ₀ < γ then μ₀ / γ else 1 - γ / (4 * μ₀); reason: the two branches of the printed constant, verbatim
--   - correction: the printed premises x^(t) ∈ 𝒳_γ and x^(t+1) ∈ 𝒳_µ, with no relation between 𝒳_γ and 𝒳_µ → the added premise hseg : segment ℝ xstar x ⊆ Xμ; reason: the printed theorem is false even when x^(t) ∈ 𝒳_µ (DISPROOF.md: n=1, 𝒳_γ=[−1,1], 𝒳_µ=[1,3], x*=0, x^(t)=1, x^(t+1)=2, γ=1, µ₀=1/10); the proof on p. 19 applies the first-order bound f(x′) ≤ f(z) + (µ₀/2)‖z − x^(t)‖² at the points z = a x* + (1 − a) x^(t), a ∈ [0, 1], which needs them in 𝒳_µ; this premise is implied by Theorems 3.1–3.2's 𝒳_γ ⊆ 𝒳_µ and excludes only steps whose segment [x*, x^(t)] leaves 𝒳_µ
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), p. 19, Theorem 7.1; §7.3, pp. 19–20; §7.6, p. 21

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework

namespace AccelMM.BTMap.Supplement

/-- Theorem 7.1, arXiv:1901.00150v3, p. 19 (corrected): the first-order-surrogate MM rate.
`g` is a first-order surrogate of `f` on `Xμ` with parameter `μ₀` in the paper's §7.6 sense:
a majorant surrogate whose error `g(·; y) − f` is differentiable and `μ₀`-smooth on `Xμ`
for every base point `y ∈ Xμ`. The segment `[x*, x]` is assumed to lie in `Xμ`; without it
the printed theorem is false (see the Formalization Note). -/
theorem theorem_7_1 {n : ℕ} (f : E n → ℝ) (g : E n → E n → ℝ)
    (Xμ Xγ : Set (E n)) (μ₀ γ : ℝ) (xstar x xnext : E n)
    (hμ₀ : 0 < μ₀) (hγ : 0 < γ)
    (hXγ : Convex ℝ Xγ)
    (hfd : ∀ u ∈ Xγ, DifferentiableAt ℝ f u)
    (hsc : StronglyConvexOn f Xγ γ)
    (hmin : ∀ z, f xstar ≤ f z)
    (hxstar : xstar ∈ Xγ)
    (hmajorant : IsMajorant g f)
    (herrd : ∀ y ∈ Xμ, ∀ u ∈ Xμ, DifferentiableAt ℝ (fun v => g v y - f v) u)
    (herr : ∀ y ∈ Xμ, SmoothOn (fun v => g v y - f v) Xμ μ₀)
    (hstep : ∀ z, g xnext x ≤ g z x)
    (hx : x ∈ Xγ) (hxnext : xnext ∈ Xμ)
    (hseg : segment ℝ xstar x ⊆ Xμ) :
    f xnext - f xstar ≤
      (if 2 * μ₀ < γ then μ₀ / γ else 1 - γ / (4 * μ₀)) * (f x - f xstar) := by sorry

end AccelMM.BTMap.Supplement
