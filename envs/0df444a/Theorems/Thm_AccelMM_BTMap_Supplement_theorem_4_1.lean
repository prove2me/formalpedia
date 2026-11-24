-- Prove2me | Theorems.Thm_AccelMM_BTMap_Supplement_theorem_4_1
-- name    : AccelMM.BTMap.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:16:42.715122+00:00
-- url     : https://prove2.me/theorems/a50218d2-9698-409d-95da-9e9fe87548f8
-- title:
--   Theorem 4.1 (companion theorem; not used in the proof of the goal) (corrected: gradient point in 𝒳) — Π-transformed gradient-descent contraction
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, let $\mathcal X$ be a convex set containing a global minimizer $x^*$ of $f$, let $d\in\mathbb R^n$ and $\mu,\gamma>0$. Assume
--
--   1. (F1) $f$ is differentiable at every point of $\mathcal X$ and $\mu$-smooth there: $\|\nabla f(u)-\nabla f(v)\|\le\mu\|u-v\|$ for $u,v\in\mathcal X$;
--   2. (F2) $f$ satisfies the $\gamma$-PL inequality $f(u)-f(x^*)\le\|\nabla f(u)\|^2/(2\gamma)$ on $\mathcal X_0=\mathcal X\cap\{u:\nabla f(u)^\top d=0\}$;
--   3. (P1) $\Pi:\mathbb R^n\to\mathbb R^n$ satisfies $f(\Pi(u))\le f(u)$ for all $u$.
--
--   Let $x\in\mathcal X_0$ and let $x^+=\Pi\bigl(x-\tfrac1\mu\nabla f(x)\bigr)$ be the $\Pi$-transformed gradient step (4.1) with $\eta=1/\mu$, with $x^+\in\mathcal X_0$. If the gradient point $x-\tfrac1\mu\nabla f(x)$ lies in $\mathcal X$, then
--   $$f(x^+)-f(x^*)\le\Bigl(1-\frac{\gamma}{\mu}\Bigr)\bigl(f(x)-f(x^*)\bigr).$$
--   This is the one-step rate of the accelerated gradient method of §4; Corollary 4.1 instantiates it for Bradley–Terry MAP estimation.
--
--   **Formalization Note** As printed, Theorem 4.1 is false: its premises constrain the iterates but not the intermediate gradient point, where the proof (§7.9, p. 22) applies the descent inequality of Theorem 3.1. The premise that this point lies in $\mathcal X$ is added; it is the analogue of Theorem 3.1's $x^{(t+1)}\in\mathcal X_\mu$ and excludes only steps whose gradient point leaves $\mathcal X$. The counterexample is in the mission's disproof record.
--
--   Differences from the source:
--   - encoding: vectors in ℝⁿ, the map Π and a step at time t → EuclideanSpace ℝ (Fin n), a function Pi, and arbitrary current and next points satisfying the update; reason: Fin n indexes coordinates from zero; universally quantifying a single step states the same claim at every admissible time
--   - encoding: (F1) f is µ-smooth on the convex set 𝒳 containing the optimum x* → Convex ℝ X, xstar ∈ X, ∀ z, f xstar ≤ f z, SmoothOn f X μ, true differentiability at every point of X, and 0 < μ, 0 < γ; reason: gradients are actual derivatives on X; positivity makes the step 1/µ and the PL denominator defined; nothing is imposed off X
--   - correction: the printed premises (F1), (F2), (P1), η = 1/µ and x^(t), x^(t+1) ∈ 𝒳₀ → the added premise hvirtual : x − (1/μ)∇f(x) ∈ X; reason: the printed theorem is false (DISPROOF.md: f(v)=vᵀAv/2 with A=[[1,1],[1,100]], 𝒳 the segment from (0,0) to (1,0), d=(1,−1), µ=2, γ=1, Π sending the gradient point (1/2,−1/2) back to (1,0)); the proof in §7.9, p. 22 applies the argument of Theorem 3.1 at the gradient point, which needs that point in the smoothness domain, as Theorem 3.1's hypothesis x^(t+1) ∈ 𝒳_µ does; only steps whose gradient point leaves 𝒳 are excluded
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), p. 11, Theorem 4.1; §4.1, p. 11, (F1), (F2), (P1), (4.1), (4.3); §7.9, p. 22

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework

namespace AccelMM.BTMap.Supplement

/-- Theorem 4.1, arXiv:1901.00150v3, p. 11 (corrected): a Π-transformed GD step.
The virtual gradient point `x - (1/μ) ∇f(x)` is assumed to lie in `X`; without it the
printed theorem is false (see the Formalization Note). -/
theorem theorem_4_1 {n : ℕ} (f : E n → ℝ) (Pi : E n → E n)
    (X : Set (E n)) (d : E n) (μ γ : ℝ) (xstar x xnext : E n)
    (hμ : 0 < μ) (hγ : 0 < γ)
    (hX : Convex ℝ X) (hxstarX : xstar ∈ X)
    (hmin : ∀ z, f xstar ≤ f z)
    (hf : ∀ u ∈ X, DifferentiableAt ℝ f u)
    (hF1 : SmoothOn f X μ)
    (hF2 : PLOn f (X0 f X d) γ xstar)
    (hP1 : ∀ u, f (Pi u) ≤ f u)
    (hstep : xnext = Pi (x - (1 / μ) • gradient f x))
    (hx : x ∈ X0 f X d) (hxnext : xnext ∈ X0 f X d)
    (hvirtual : x - (1 / μ) • gradient f x ∈ X) :
    f xnext - f xstar ≤ (1 - γ / μ) * (f x - f xstar) := by sorry

end AccelMM.BTMap.Supplement
