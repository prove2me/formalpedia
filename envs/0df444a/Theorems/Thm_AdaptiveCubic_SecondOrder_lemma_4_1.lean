-- Prove2me | Theorems.Thm_AdaptiveCubic_SecondOrder_lemma_4_1
-- name    : AdaptiveCubic.SecondOrder.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:15.682029+00:00
-- url     : https://prove2.me/theorems/d1fbf85d-e950-4ba0-a01c-b46f7fa20c52
-- title:
--   Lemma 4.1 — properties of a global minimizer of the model over a subspace
-- statement:
--   Let $B_k$ be symmetric and $\sigma_k>0$, and suppose $s_k$ is a global minimizer of the cubic model $m_k(s)$ over a subspace $\mathcal L_k$ of $\mathbb R^n$. Then $s_k$ satisfies
--
--   $$g_k^\top s_k + s_k^\top B_ks_k + \sigma_k\|s_k\|^3 = 0 \quad (4.1), \qquad s_k^\top B_ks_k+\sigma_k\|s_k\|^3\ge0 \quad (4.2),$$
--
--   and, for any matrix $Q_k$ with orthonormal columns forming a basis of $\mathcal L_k$,
--
--   $$Q_k^\top B_kQ_k + \sigma_k\|s_k\|\,I \ \text{ is positive semidefinite.} \qquad (4.3)$$
--
--   In particular a global minimizer of $m_k$ over all of $\mathbb R^n$ satisfies (4.1) and (4.2) (the case $\mathcal L_k=\mathbb R^n$).
--
--   The lemma shows that minimizing the model over subspaces, as ARC(S) does, produces steps meeting (4.1)–(4.2), and it relates the step length to the curvature of $B_k$ inside the subspace.
--
--   **Formalization Note** Positive semidefiniteness (4.3) is stated basis-free: $v^\top B_kv+\sigma_k\|s_k\|\,\|v\|^2\ge0$ for every $v\in\mathcal L_k$, which is the quadratic form of $Q_k^\top B_kQ_k+\sigma_k\|s_k\|I$ at $y$ with $v=Q_ky$. The lemma is stated for a single model with arbitrary data $f$, $x_k$, $B_k$, $\sigma_k$.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 11, Lemma 4.1

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_model

open scoped RealInnerProductSpace

namespace AdaptiveCubic.SecondOrder

/-- Lemma 4.1, p. 11 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009; proof in
Part I, Lemma 3.2). If `s_k` is a global minimizer of the cubic AdaptiveCubic.Cauchy.model `m_k(s)` (1.2) over a
subspace `L_k` of `ℝⁿ` (with `B_k` symmetric and `σ_k > 0`), then `s_k` satisfies (4.1),
`g_kᵀ s_k + s_kᵀ B_k s_k + σ_k‖s_k‖³ = 0`, and (4.2), `s_kᵀ B_k s_k + σ_k‖s_k‖³ ≥ 0`, and
`Q_kᵀ B_k Q_k + σ_k‖s_k‖ I` is positive semidefinite (4.3) for any `Q_k` with orthonormal columns
spanning `L_k`, stated as `vᵀ B_k v + σ_k‖s_k‖‖v‖² ≥ 0` for every `v ∈ L_k` (`v = Q_k y`).
The page's last sentence (global minimizer over `ℝⁿ`) is the case `L_k = ⊤`. -/
theorem lemma_4_1 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hB : IsSelfAdjoint B)
    (σ : ℝ) (hσ : 0 < σ) (x : EuclideanSpace ℝ (Fin n))
    (Lk : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (sk : EuclideanSpace ℝ (Fin n))
    (hsL : sk ∈ Lk) (hmin : ∀ t ∈ Lk, AdaptiveCubic.Cauchy.model f B σ x sk ≤ AdaptiveCubic.Cauchy.model f B σ x t) :
    ⟪gradient f x, sk⟫ + ⟪sk, B sk⟫ + σ * ‖sk‖ ^ 3 = 0 ∧
    0 ≤ ⟪sk, B sk⟫ + σ * ‖sk‖ ^ 3 ∧
    ∀ v ∈ Lk, 0 ≤ ⟪v, B v⟫ + σ * ‖sk‖ * ‖v‖ ^ 2 := by sorry

end AdaptiveCubic.SecondOrder
