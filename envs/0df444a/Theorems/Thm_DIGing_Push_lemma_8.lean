-- Prove2me | Theorems.Thm_DIGing_Push_lemma_8
-- name    : DIGing.Push.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:56:13.511499+00:00
-- url     : https://prove2.me/theorems/6cb6d85d-a002-4858-8504-7d9e9c7b3c4e
-- title:
--   Lemma 8, p. 12 — error bound on the inexact gradient method: |r|^{λ,K} ≤ 2r⁰ + (λ√n)⁻¹√(L(1+η)/(μ̄η) + (μ̂/μ̄)β) Σᵢ‖p − sᵢ‖^{λ,K}_F
-- statement:
--   Let $g=\frac1n\sum_{i=1}^n g_i$ where the $g_i:\mathbb R^p\to\mathbb R$ satisfy Assumptions 4 and 5 (with constants $L_i$, $\mu_i$), and let $p^*$ be a global minimizer of $g$. Consider the **inexact gradient method**
--   $$p^{k+1}=p^k-\theta\,\frac1n\sum_{i=1}^n\nabla g_i(s_i^k),$$
--   where $s_1^k,\dots,s_n^k\in\mathbb R^p$ are arbitrary points, and put $r^k=\|p^k-p^*\|$. Suppose that $\beta>0$, $\eta>0$ and
--   $$\sqrt{1-\frac{\theta\bar\mu\beta}{\beta+1}}\le\lambda<1,\qquad \theta\le\frac1{(1+\eta)\bar L}.$$
--   Then for every $K=0,1,\dots$
--   $$|r|^{\lambda,K}\le 2r^0+(\lambda\sqrt n)^{-1}\sqrt{\frac{L(1+\eta)}{\bar\mu\eta}+\frac{\hat\mu}{\bar\mu}\beta}\;\sum_{i=1}^n\|p-s_i\|_F^{\lambda,K}.$$
--
--   The lemma converts gradient errors into an error bound for the averaged iterate; in the Push-DIGing analysis it is applied to the average $\bar{\mathbf u}(k)$ with $s_i^k=x_i(k)$, giving Lemma 17.
--
--   **Formalization Note** The iterate is named `pp` because `p` is the dimension. $|r|^{\lambda,K}$ and $\|p-s_i\|_F^{\lambda,K}$ are the truncated ergodic norms of $k\mapsto\|p^k-p^*\|$ and $k\mapsto\|p^k-s_i^k\|$. This statement is identical to the one in the companion DIGing mission.
-- source:
--   arXiv:1607.03218v3, Lemma 8, (18), (19), p. 12

import Mathlib
import Definitions.Def_DIGing_Undir_Common

namespace DIGing.Push

theorem lemma_8 {n p : ℕ} (g : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lc mu : Fin n → ℝ)
    (h4 : DIGing.Undir.Assumption4 g Lc) (h5 : DIGing.Undir.Assumption5 g mu)
    (pstar : EuclideanSpace ℝ (Fin p)) (hpstar : ∀ z, DIGing.Undir.objective g pstar ≤ DIGing.Undir.objective g z)
    (θ β η lam : ℝ) (hβ : 0 < β) (hη : 0 < η)
    (hlam : Real.sqrt (1 - θ * DIGing.Undir.mubar mu * β / (β + 1)) ≤ lam) (hlam1 : lam < 1)
    (hθ : θ ≤ 1 / ((1 + η) * DIGing.Undir.Lbar Lc))
    (pp : ℕ → EuclideanSpace ℝ (Fin p)) (s : Fin n → ℕ → EuclideanSpace ℝ (Fin p))
    (hrec : ∀ k, pp (k + 1) = pp k - θ • ((1 / (n : ℝ)) • ∑ i, gradient (g i) (s i k))) :
    ∀ K : ℕ, DIGing.Undir.ergK lam K (fun k => ‖pp k - pstar‖) ≤
      2 * ‖pp 0 - pstar‖ + (lam * Real.sqrt n)⁻¹ *
        Real.sqrt (DIGing.Undir.Lmax Lc * (1 + η) / (DIGing.Undir.mubar mu * η) + DIGing.Undir.muhat mu / DIGing.Undir.mubar mu * β) *
        ∑ i, DIGing.Undir.ergK lam K (fun k => ‖pp k - s i k‖) := by sorry

end DIGing.Push
