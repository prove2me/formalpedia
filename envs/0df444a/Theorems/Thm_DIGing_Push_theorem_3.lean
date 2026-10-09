-- Prove2me | Theorems.Thm_DIGing_Push_theorem_3
-- name    : DIGing.Push.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:02.876709+00:00
-- url     : https://prove2.me/theorems/4fc1aa05-b104-4090-92b5-d8efe30d8501
-- title:
--   Theorem 3, p. 9 — the small gain theorem: ‖s¹‖^λ_F ≤ (ω₁γ₂⋯γ_m + ⋯ + ω_m)/(1 − γ₁⋯γ_m)
-- statement:
--   Let $\lambda\in(0,1)$ and let $\mathbf s^1,\dots,\mathbf s^m$ ($m\ge1$) be sequences of $n\times p$ matrices. Suppose that for all positive integers $K$ and each $i=1,\dots,m$ there is an arrow $\mathbf s^i\to\mathbf s^{(i\bmod m)+1}$, that is,
--   $$\|\mathbf s^{(i\bmod m)+1}\|_F^{\lambda,K}\le\gamma_i\|\mathbf s^i\|_F^{\lambda,K}+\omega_i,$$
--   where the gains $\gamma_1,\dots,\gamma_m$ are nonnegative and $\gamma_1\gamma_2\cdots\gamma_m<1$. Then for every $k\ge0$
--   $$\frac{1}{\lambda^k}\|\mathbf s^1(k)\|_F\le\frac{1}{1-\gamma_1\gamma_2\cdots\gamma_m}\big(\omega_1\gamma_2\gamma_3\cdots\gamma_m+\omega_2\gamma_3\cdots\gamma_m+\cdots+\omega_{m-1}\gamma_m+\omega_m\big),$$
--   that is, $\|\mathbf s^1\|^\lambda_F=\sup_k\lambda^{-k}\|\mathbf s^1(k)\|_F$ is bounded by the right-hand side.
--
--   This is the device that turns the four arrows of the Push-DIGing analysis into a bound on the optimality error.
--
--   **Formalization Note** Indices are 0-based: $\mathbf s^1$ is `s ⟨0, hm⟩` and the arrow $\mathbf s^i\to\mathbf s^{(i\bmod m)+1}$ is `i ↦ finRotate m i`. The bracket is written $\sum_j\omega_j\prod_{l>j}\gamma_l$. The supremum, which may be infinite, is stated pointwise in $k$. This statement is identical to the one in the companion DIGing mission.
-- source:
--   arXiv:1607.03218v3, Theorem 3, (7), p. 9

import Mathlib
import Definitions.Def_DIGing_Undir_Common

namespace DIGing.Push

theorem theorem_3 {n p m : ℕ} (hm : 0 < m) (s : Fin m → ℕ → DIGing.Undir.Stack n p) (lam : ℝ)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (γ ω : Fin m → ℝ) (hγ : ∀ i, 0 ≤ γ i)
    (hprod : ∏ i, γ i < 1)
    (harrow : ∀ K : ℕ, 0 < K → ∀ i : Fin m,
      DIGing.Undir.ergK lam K (fun k => DIGing.Undir.frob (s (finRotate m i) k)) ≤ γ i * DIGing.Undir.ergK lam K (fun k => DIGing.Undir.frob (s i k)) + ω i) :
    ∀ k : ℕ, DIGing.Undir.frob (s ⟨0, hm⟩ k) / lam ^ k ≤
      (1 - ∏ i, γ i)⁻¹ * ∑ j, ω j * ∏ l ∈ Finset.univ.filter (fun l => j < l), γ l := by sorry

end DIGing.Push
