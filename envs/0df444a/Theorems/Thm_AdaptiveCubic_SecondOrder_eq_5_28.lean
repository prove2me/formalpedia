-- Prove2me | Theorems.Thm_AdaptiveCubic_SecondOrder_eq_5_28
-- name    : AdaptiveCubic.SecondOrder.eq_5_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:18.103996+00:00
-- url     : https://prove2.me/theorems/f2fdab9a-4514-4cac-8252-4f4e81d4ce35
-- title:
--   (5.28) — negative curvature in the subspace forces σ_k‖s_k‖ ≥ |λ_min(Q_kᵀB_kQ_k)|
-- statement:
--   Consider a run of ARC(S) with $\sigma_k\ge\sigma_{\min}>0$ for all $k$ (2.11), in which each step $s_k$ is a global minimizer of $m_k$ over a subspace $\mathcal L_k$ spanned by the orthonormal columns of $Q_k$. Let $\epsilon>0$. Then
--
--   $$\sigma_k\|s_k\|\ \ge\ |\lambda_{\min}(Q_k^\top B_kQ_k)| \quad\text{for any } k\ge0 \text{ such that } -\lambda_{\min}(Q_k^\top B_kQ_k)>\epsilon.$$
--
--   Negative curvature in the subspace forces a step that is long relative to $1/\sigma_k$; combined with Lemma 4.2 this turns curvature into a decrease of the model.
--
--   **Formalization Note** $\lambda_{\min}(Q_k^\top B_kQ_k)$ is the Rayleigh-quotient minimum of $B_k$ over unit vectors of $\mathcal L_k$ (definition `lamMin`). The subspace minimizer condition is $s_k\in\mathcal L_k$ and $m_k(s_k)\le m_k(t)$ for every $t\in\mathcal L_k$.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 16, proof of Corollary 5.4, (5.28)

import Mathlib
import Definitions.Def_AdaptiveCubic_SecondOrder_IsARCSRun
import Definitions.Def_AdaptiveCubic_SecondOrder_lamMin

open scoped RealInnerProductSpace

namespace AdaptiveCubic.SecondOrder

/-- Proof of Corollary 5.4, (5.28), p. 16 (Cartis, Gould & Toint, ARC Part II, preprint rev.
15 Sep 2009). If `s_k` is a global minimizer of `m_k` over the subspace `L_k`, then
`σ_k‖s_k‖ ≥ |λ_min(Q_kᵀB_kQ_k)|` for every `k ≥ 0` with `−λ_min(Q_kᵀB_kQ_k) > ε`.
Hypotheses: ARC(S) run (Algorithm 4.1), (2.11) `σ_k ≥ σ_min > 0`, the subspace minimizer
condition of Corollary 5.4, `ε > 0`. `λ_min(Q_kᵀB_kQ_k)` is `lamMin (B k) (Lsub k)`. -/
theorem eq_5_28 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ κθ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : IsARCSRun f γ₁ γ₂ η₁ η₂ κθ x s σ B)
    (σmin : ℝ) (hσmin : 0 < σmin) (h211 : ∀ k, σmin ≤ σ k)
    (Lsub : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hsL : ∀ k, s k ∈ Lsub k)
    (hmin : ∀ k, ∀ t ∈ Lsub k,
      AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) ≤ AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) t)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ k, ε < -lamMin (B k) (Lsub k) → |lamMin (B k) (Lsub k)| ≤ σ k * ‖s k‖ := by sorry

end AdaptiveCubic.SecondOrder
