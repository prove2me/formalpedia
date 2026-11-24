-- Prove2me | Theorems.Thm_AccelMM_BTMap_Supplement_theorem_3_1
-- name    : AccelMM.BTMap.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:14:07.498914+00:00
-- url     : https://prove2.me/theorems/7de3c69a-b3f3-41c3-a173-1f593d06f114
-- title:
--   Theorem 3.1 (companion theorem; not used in the proof of the goal) — local gradient-descent contraction
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex on a convex set $X_\mu$, differentiable at every point of $X_\mu$, and have a $\mu$-Lipschitz gradient there, where $\mu>0$. Let $\gamma>0$, let $X_\gamma\subseteq X_\mu$, and let $x^*\in X_\gamma$ be a global minimizer of $f$. Assume that
--   $$f(u)-f(x^*)\le\frac{\|\nabla f(u)\|^2}{2\gamma}\qquad(u\in X_\gamma).$$
--   For any current point $x\in X_\gamma$, set $x^+=x-\nabla f(x)/\mu$. If $x^+\in X_\mu$, then
--   $$f(x^+)-f(x^*)\le\left(1-\frac{\gamma}{\mu}\right)\bigl(f(x)-f(x^*)\bigr).$$
--   This is the local one-step gradient-descent rate. It supplies the paper's comparison with the MM rate while retaining separate smoothness and PL domains.
--
--   Differences from the source:
--   - encoding: vectors in ℝⁿ and a step at time t → EuclideanSpace ℝ (Fin n) and arbitrary current and next points satisfying the update; reason: Fin n indexes coordinates from zero; universally quantifying a single step states the same claim at every admissible time
--   - reading: a convex µ-smooth function on X_µ → ConvexOn ℝ Xμ f, including convexity of Xμ; reason: the descent inequality (2.11), PDF p. 7, and its application in §§7.1–7.2 use the segment between the two smoothness-domain points; this is the convex ambient domain recorded in the source context
--   - encoding: gradients, positive-step smoothness and the γ-PL inequality → true differentiability at every point of Xμ and explicit μ>0 and γ>0; reason: smoothness is local and gradients are actual derivatives there; positivity makes the step and PL denominators defined, without imposing differentiability, smoothness or PL outside the indicated domains
--   - encoding: x* is a minimizer and gradient descent uses η=1/µ → ∀ z, f xstar ≤ f z and xnext = x − (1/μ) • gradient f x; reason: the attained global minimum and one update are expressed directly, without choosing an argmin or assuming a full infinite run
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), p. 7, Theorem 3.1; §7.1, pp. 18–19

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework

namespace AccelMM.BTMap.Supplement

/-- Theorem 3.1, arXiv:1901.00150v3, p. 7: a local-domain GD step. -/
theorem theorem_3_1 {n : ℕ} (f : E n → ℝ)
    (Xμ Xγ : Set (E n)) (μ γ : ℝ) (xstar x xnext : E n)
    (hμ : 0 < μ) (hγ : 0 < γ)
    (hf : ∀ u ∈ Xμ, DifferentiableAt ℝ f u)
    (hconv : ConvexOn ℝ Xμ f)
    (hsmooth : SmoothOn f Xμ μ)
    (hsub : Xγ ⊆ Xμ)
    (hPL : PLOn f Xγ γ xstar)
    (hxstar : xstar ∈ Xγ)
    (hmin : ∀ z, f xstar ≤ f z)
    (hx : x ∈ Xγ)
    (hstep : xnext = x - (1 / μ) • gradient f x)
    (hxnext : xnext ∈ Xμ) :
    f xnext - f xstar ≤ (1 - γ / μ) * (f x - f xstar) := by sorry

end AccelMM.BTMap.Supplement
