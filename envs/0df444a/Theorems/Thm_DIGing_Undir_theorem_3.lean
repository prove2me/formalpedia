-- Prove2me | Theorems.Thm_DIGing_Undir_theorem_3
-- name    : DIGing.Undir.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:12.048137+00:00
-- url     : https://prove2.me/theorems/e9042214-592f-414d-b21e-3ff7fd0e2e45
-- title:
--   Theorem 3, p. 9 — small gain theorem: a cycle of arrows with γ₁⋯γ_m < 1 bounds ‖s¹‖^λ_F
-- statement:
--   Let $\lambda\in(0,1)$, let $m\ge1$, and let $\mathbf s^1,\dots,\mathbf s^m$ be sequences of $n\times p$ matrices. Suppose that for every positive integer $K$ and every $i=1,\dots,m$ there is an arrow $\mathbf s^i\to\mathbf s^{(i\bmod m)+1}$, that is,
--   $$\|\mathbf s^{(i\bmod m)+1}\|_F^{\lambda,K}\le\gamma_i\|\mathbf s^i\|_F^{\lambda,K}+\omega_i,$$
--   where the gains $\gamma_1,\dots,\gamma_m$ are nonnegative and $\gamma_1\gamma_2\cdots\gamma_m<1$. Then
--   $$\|\mathbf s^1\|_F^\lambda=\sup_{k\ge0}\lambda^{-k}\|\mathbf s^1(k)\|_F\le\frac{1}{1-\gamma_1\cdots\gamma_m}\big(\omega_1\gamma_2\gamma_3\cdots\gamma_m+\omega_2\gamma_3\cdots\gamma_m+\cdots+\omega_{m-1}\gamma_m+\omega_m\big).$$
--
--   This is the small gain theorem in the ergodic norm, the organizing principle of the paper: the convergence proof establishes the four arrows of a cycle and then reads off a bound on $\sup_k\lambda^{-k}\|\mathbf q(k)\|_F$, i.e. an R-linear rate.
--
--   **Formalization Note.** Indices are $0$-based: $\mathbf s^1$ is `s ⟨0, hm⟩` and the successor $(i\bmod m)+1$ is `finRotate m i`. The bound is $\sum_j\omega_j\prod_{l>j}\gamma_l$. The supremum, which may be infinite in general, is stated pointwise: $\lambda^{-k}\|\mathbf s^1(k)\|_F\le U$ for every $k$.
-- source:
--   Nedić, Olshevsky & Shi, arXiv:1607.03218v3, Theorem 3, display (7), p. 9

import Mathlib
import Definitions.Def_DIGing_Undir_Common

namespace DIGing.Undir

theorem theorem_3 {n p m : ℕ} (hm : 0 < m) (s : Fin m → ℕ → Stack n p) (lam : ℝ)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (γ ω : Fin m → ℝ) (hγ : ∀ i, 0 ≤ γ i)
    (hprod : ∏ i, γ i < 1)
    (harrow : ∀ K : ℕ, 0 < K → ∀ i : Fin m,
      ergK lam K (fun k => frob (s (finRotate m i) k)) ≤ γ i * ergK lam K (fun k => frob (s i k)) + ω i) :
    ∀ k : ℕ, frob (s ⟨0, hm⟩ k) / lam ^ k ≤
      (1 - ∏ i, γ i)⁻¹ * ∑ j, ω j * ∏ l ∈ Finset.univ.filter (fun l => j < l), γ l := by sorry

end DIGing.Undir
