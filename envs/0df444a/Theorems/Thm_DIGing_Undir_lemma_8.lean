-- Prove2me | Theorems.Thm_DIGing_Undir_lemma_8
-- name    : DIGing.Undir.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:18.084415+00:00
-- url     : https://prove2.me/theorems/6721952a-6ea5-4002-a7a6-a65aa6233e64
-- title:
--   Lemma 8, p. 12 — error bound on inexact gradient descent: |r|^{λ,K} ≤ 2r⁰ + (λ√n)⁻¹√(L(1+η)/(μ̄η) + (μ̂/μ̄)β) Σᵢ‖p − sᵢ‖^{λ,K}_F
-- statement:
--   Let $g_1,\dots,g_n:\mathbb R^p\to\mathbb R$ satisfy Assumptions 4 and 5 (with constants $L_i$, $\mu_i$), let $g=\frac1n\sum_ig_i$ and let $p^*$ be a global minimizer of $g$. Consider the inexact gradient method (18),
--   $$p^{k+1}=p^k-\theta\,\frac1n\sum_{i=1}^n\nabla g_i(s_i^k),$$
--   driven by arbitrary points $s_i^k\in\mathbb R^p$, and put $r^k=\|p^k-p^*\|$. Suppose that $\beta>0$, $\eta>0$ and
--   $$\sqrt{1-\frac{\theta\bar\mu\beta}{\beta+1}}\le\lambda<1,\qquad\theta\le\frac{1}{(1+\eta)\bar L}.$$
--   Then for every $K=0,1,\dots$,
--   $$|r|^{\lambda,K}\le2r^0+(\lambda\sqrt n)^{-1}\sqrt{\frac{L(1+\eta)}{\bar\mu\eta}+\frac{\hat\mu}{\bar\mu}\beta}\;\sum_{i=1}^n\|p-s_i\|_F^{\lambda,K}.$$
--
--   Gradient descent on a strongly convex smooth sum converges linearly even when each component gradient is evaluated at a perturbed point; this lemma quantifies the perturbation's effect in the ergodic norm. It is the key ingredient of the last arrow (Lemma 9), with $p^k=\bar x(k)$ and $s_i^k=x_i(k)$.
--
--   **Formalization Note.** $\|p-s_i\|_F^{\lambda,K}$ is the ergodic norm of $k\mapsto\|p^k-s_i^k\|$. The square root covers both terms, as on the page.
-- source:
--   Nedić, Olshevsky & Shi, arXiv:1607.03218v3, Lemma 8, display (19), p. 12 (method (18) and r^k, p. 12)

import Mathlib
import Definitions.Def_DIGing_Undir_Common

namespace DIGing.Undir

theorem lemma_8 {n p : ℕ} (g : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lc mu : Fin n → ℝ)
    (h4 : Assumption4 g Lc) (h5 : Assumption5 g mu)
    (pstar : EuclideanSpace ℝ (Fin p)) (hpstar : ∀ z, objective g pstar ≤ objective g z)
    (θ β η lam : ℝ) (hβ : 0 < β) (hη : 0 < η)
    (hlam : Real.sqrt (1 - θ * mubar mu * β / (β + 1)) ≤ lam) (hlam1 : lam < 1)
    (hθ : θ ≤ 1 / ((1 + η) * Lbar Lc))
    (pp : ℕ → EuclideanSpace ℝ (Fin p)) (s : Fin n → ℕ → EuclideanSpace ℝ (Fin p))
    (hrec : ∀ k, pp (k + 1) = pp k - θ • ((1 / (n : ℝ)) • ∑ i, gradient (g i) (s i k))) :
    ∀ K : ℕ, ergK lam K (fun k => ‖pp k - pstar‖) ≤
      2 * ‖pp 0 - pstar‖ + (lam * Real.sqrt n)⁻¹ *
        Real.sqrt (Lmax Lc * (1 + η) / (mubar mu * η) + muhat mu / mubar mu * β) *
        ∑ i, ergK lam K (fun k => ‖pp k - s i k‖) := by sorry

end DIGing.Undir
