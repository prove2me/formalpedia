-- Prove2me | Theorems.Thm_AccelMM_BTMap_Supplement_theorem_3_2
-- name    : AccelMM.BTMap.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:15:17.810523+00:00
-- url     : https://prove2.me/theorems/d12f2886-5850-4fc5-a932-a79e4dd41a85
-- title:
--   Theorem 3.2 (companion theorem; not used in the proof of the goal) — local MM contraction
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex on a convex set $X_\mu$, differentiable at every point of $X_\mu$, and have a $\mu$-Lipschitz gradient there. Let $\mu,\gamma,\delta>0$, $X_\gamma\subseteq X_\mu$, and let $x^*\in X_\gamma$ be a global minimizer of $f$. Assume the $\gamma$-PL inequality
--   $$f(u)-f(x^*)\le\frac{\|\nabla f(u)\|^2}{2\gamma}\qquad(u\in X_\gamma).$$
--   Let $g(u;v)$ be a touching global majorant: $f(u)\le g(u;v)$ and $g(u;u)=f(u)$ for every $u,v$. Suppose
--   $$g(u;v)-f(u)\le\frac{\delta}{2}\|u-v\|^2\qquad(u,v\in X_\mu).$$
--   For any $x\in X_\gamma$ and any global minimizer $x^+$ of $g(\cdot;x)$, if $x-\nabla f(x)/(\mu+\delta)\in X_\mu$, then
--   $$f(x^+)-f(x^*)\le\left(1-\frac{\gamma}{\mu+\delta}\right)\bigl(f(x)-f(x^*)\bigr).$$
--   This is the local one-step MM rate. The domain premise concerns the virtual gradient point; the MM output may lie anywhere in $\mathbb R^n$.
--
--   Differences from the source:
--   - encoding: vectors in ℝⁿ and a step at time t → EuclideanSpace ℝ (Fin n) and arbitrary current and next points satisfying the update; reason: Fin n indexes coordinates from zero; universally quantifying a single step states the same claim at every admissible time
--   - reading: a convex µ-smooth function on X_µ → ConvexOn ℝ Xμ f, including convexity of Xμ; reason: the descent inequality (2.11), PDF p. 7, and its application in §§7.1–7.2 use the segment between the two smoothness-domain points; this is the convex ambient domain recorded in the source context
--   - encoding: gradients, positive-step smoothness and the γ-PL inequality → true differentiability at every point of Xμ and explicit μ>0 and γ>0; reason: smoothness is local and gradients are actual derivatives there; positivity makes the step and PL denominators defined, without imposing differentiability, smoothness or PL outside the indicated domains
--   - encoding: x* is a minimizer and the algorithm takes an argmin step → an explicit global minimizer xstar and a relational step for arbitrary xnext; reason: an attained minimum is expressed by comparison with every point, without a choice function, real infimum or uniqueness requirement
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), p. 8, Theorem 3.2; §7.2, p. 19

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework

namespace AccelMM.BTMap.Supplement

/-- Theorem 3.2, arXiv:1901.00150v3, p. 8: a local-domain MM step.
The MM output is unrestricted; the virtual gradient point belongs to `Xμ`. -/
theorem theorem_3_2 {n : ℕ} (f : E n → ℝ) (g : E n → E n → ℝ)
    (Xμ Xγ : Set (E n)) (μ γ δ : ℝ) (xstar x xnext : E n)
    (hμ : 0 < μ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hf : ∀ u ∈ Xμ, DifferentiableAt ℝ f u)
    (hconv : ConvexOn ℝ Xμ f)
    (hsmooth : SmoothOn f Xμ μ)
    (hsub : Xγ ⊆ Xμ)
    (hPL : PLOn f Xγ γ xstar)
    (hxstar : xstar ∈ Xγ)
    (hmin : ∀ z, f xstar ≤ f z)
    (hmajorant : IsMajorant g f)
    (hgap : ∀ u ∈ Xμ, ∀ v ∈ Xμ,
      g u v - f u ≤ δ / 2 * ‖u - v‖ ^ 2)
    (hx : x ∈ Xγ)
    (hstep : ∀ z, g xnext x ≤ g z x)
    (hvirtual : x - (1 / (μ + δ)) • gradient f x ∈ Xμ) :
    f xnext - f xstar ≤ (1 - γ / (μ + δ)) * (f x - f xstar) := by sorry

end AccelMM.BTMap.Supplement
