-- Prove2me | Theorems.Thm_AccelMM_BTMap_theorem_4_2
-- name    : AccelMM.BTMap.theorem_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:33:14.910977+00:00
-- url     : https://prove2.me/theorems/efe3b5ea-e606-4486-8b43-7d884a3e4b34
-- title:
--   Theorem 4.2, pp. 11–12 — one Π-transformed MM step is an improvement (rate corrected to γ/(µ + δ))
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be differentiable, $\mathcal X$ a convex set containing a minimizer $x^*$ of $f$, $d\in\mathbb R^n$, and $\mu,\gamma,\delta>0$. Assume
--
--   1. (F1) $f$ is $\mu$-smooth on $\mathcal X$;
--   2. (F2) $f$ satisfies the $\gamma$-PL inequality on $\mathcal X_0=\mathcal X\cap\{x:\nabla f(x)^\top d=0\}$;
--   3. (P1) $\Pi:\mathbb R^n\to\mathbb R^n$ satisfies $f(\Pi(x))\le f(x)$ for all $x$;
--   4. $g$ is a majorant surrogate of $f$ with $g(x;y)-f(x)\le\frac\delta2\|x-y\|^2$ for all $x,y\in\mathcal X$.
--
--   Let $x^{(t)}\in\mathcal X_0$, let $x'$ be a minimizer of $g(\cdot\,;x^{(t)})$, and let $x^{(t+1)}=\Pi(x')$ (the $\Pi$-transformed MM step (4.2)), with $x^{(t+1)}\in\mathcal X_0$. If moreover the virtual gradient point $x^{(t)}-\frac{1}{\mu+\delta}\nabla f(x^{(t)})$ lies in $\mathcal X$, then
--   $$f(x^{(t+1)})-f(x^*)\le\Bigl(1-\frac{\gamma}{\mu+\delta}\Bigr)\bigl(f(x^{(t)})-f(x^*)\bigr).$$
--
--   This is the general one-step rate of the accelerated MM method; Corollary 4.2 instantiates it for the Bradley–Terry MAP problem.
--
--   **Formalization Note** The page prints the rate $\gamma/(\gamma+\delta)$; the argument (and Corollary 4.2, whose rate is $\gamma/(\mu+\delta)$) gives $\gamma/(\mu+\delta)$, which is stated here. The surrogate bound is assumed on $\mathcal X$ only, a weaker hypothesis than the printed global bound. The condition that the virtual gradient point lies in $\mathcal X$ is the hypothesis of the paper's Theorem 3.2 (p. 8), which the proof of Theorem 4.2 reuses; it is added here. $f$ is assumed differentiable because the gradient is used.
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), pp. 11–12, Theorem 4.2 (rate corrected; virtual-point condition from Theorem 3.2, p. 8)

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework

namespace AccelMM.BTMap

theorem theorem_4_2 {n : ℕ} (f : E n → ℝ) (hf : Differentiable ℝ f)
    (X : Set (E n)) (hX : Convex ℝ X) (xstar : E n) (hxstarX : xstar ∈ X)
    (hmin : ∀ x, f xstar ≤ f x) (d : E n) (μ γ δ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hF1 : SmoothOn f X μ) (hF2 : PLOn f (X0 f X d) γ xstar)
    (Pi : E n → E n) (hP1 : ∀ x, f (Pi x) ≤ f x)
    (g : E n → E n → ℝ) (hg : IsMajorant g f)
    (hgδ : ∀ x ∈ X, ∀ y ∈ X, g x y - f x ≤ δ / 2 * ‖x - y‖ ^ 2)
    (xt xm xt1 : E n) (hxt : xt ∈ X0 f X d) (hxt1 : xt1 ∈ X0 f X d)
    (hvirt : xt - (1 / (μ + δ)) • gradient f xt ∈ X)
    (hxm : ∀ z, g xm xt ≤ g z xt) (hstep : xt1 = Pi xm) :
    f xt1 - f xstar ≤ (1 - γ / (μ + δ)) * (f xt - f xstar) := by sorry

end AccelMM.BTMap
