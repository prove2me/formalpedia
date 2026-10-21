-- Prove2me | Theorems.Thm_AccelMM_BTMap_lemma_4_1
-- name    : AccelMM.BTMap.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:33:11.969425+00:00
-- url     : https://prove2.me/theorems/3071ad7d-16d5-4157-9550-1a74c8b926fe
-- title:
--   Lemma 4.1, p. 12 — a Hessian lower bound A_𝒳 gives the γ-PL inequality on 𝒳₀ for γ ≤ γ₀
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and twice differentiable, $\mathcal X\subseteq\mathbb R^n$ convex, $d\in\mathbb R^n$ nonzero, $\mathcal X_0=\mathcal X\cap\{x:\nabla f(x)^\top d=0\}$, and $x^*\in\mathcal X_0$ a minimizer of $f$. Let $A_{\mathcal X}$ be a positive semidefinite matrix such that
--
--   1. (A1) $\nabla^2f(x)\succeq A_{\mathcal X}$ for all $x\in\mathcal X$, and
--   2. (A2) $u^\top A_{\mathcal X}v=0$ whenever $u=(I-P_d)z$ and $v=P_dz$ for some $z\in\mathbb R^n$, where $P_d=I-\frac{1}{\|d\|^2}dd^\top$.
--
--   Then $f$ satisfies the $\gamma$-PL inequality on $\mathcal X_0$ for every $\gamma>0$ with $\gamma\le\gamma_0$, where
--   $$\gamma_0=\min_{x\in\mathbb R^n\setminus\{0\}:\,d^\top x=0}\frac{x^\top A_{\mathcal X}x}{\|x\|^2};$$
--   that is, $f(x)-f(x^*)\le\frac{1}{2\gamma}\|\nabla f(x)\|^2$ for all $x\in\mathcal X_0$.
--
--   The lemma turns a curvature bound that holds only in directions orthogonal to $d$ into a PL inequality on the points where the gradient is orthogonal to $d$.
--
--   **Formalization Note** "$\gamma\le\gamma_0$" is encoded as $\gamma\le x^\top A_{\mathcal X}x/\|x\|^2$ for every nonzero $x$ with $d^\top x=0$, which avoids a minimum over a possibly empty set (when $n\le1$). Twice differentiability means that $f$ and its Fréchet derivative are differentiable; (A1) compares quadratic forms with the second iterated Fréchet derivative. $d\ne0$ is implicit in the page's $1/\|d\|^2$. "Minimizer" is a global minimizer; $\gamma>0$ is required by (2.12).
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), p. 12, Lemma 4.1

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework

namespace AccelMM.BTMap

open scoped InnerProductSpace

theorem lemma_4_1 {n : ℕ} (f : E n → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hf : Differentiable ℝ f) (hf2 : Differentiable ℝ (fderiv ℝ f))
    (X : Set (E n)) (hX : Convex ℝ X) (d : E n) (hd : d ≠ 0)
    (xstar : E n) (hxstar : xstar ∈ X0 f X d) (hmin : ∀ x, f xstar ≤ f x)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hA1 : ∀ x ∈ X, ∀ v : E n, v.ofLp ⬝ᵥ A.mulVec v.ofLp ≤ iteratedFDeriv ℝ 2 f x ![v, v])
    (hA2 : ∀ z : Fin n → ℝ,
      ((1 - projD d).mulVec z) ⬝ᵥ A.mulVec ((projD d).mulVec z) = 0) :
    ∀ γ : ℝ, 0 < γ →
      (∀ x : E n, ⟪d, x⟫_ℝ = 0 → x ≠ 0 → γ ≤ x.ofLp ⬝ᵥ A.mulVec x.ofLp / ‖x‖ ^ 2) →
      PLOn f (X0 f X d) γ xstar := by sorry

end AccelMM.BTMap
