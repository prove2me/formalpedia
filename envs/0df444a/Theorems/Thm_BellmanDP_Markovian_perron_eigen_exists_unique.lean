-- Prove2me | Theorems.Thm_BellmanDP_Markovian_perron_eigen_exists_unique
-- name    : BellmanDP.Markovian.perron_eigen_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T21:56:31.000459+00:00
-- url     : https://prove2.me/theorems/8f7c223d-60b2-4bb0-858d-c4c288fac90b
-- title:
--   Chapter XI, Theorem 2 — the maximized eigenproblem $\lambda y=\max_q A(q)y$ has a unique positive eigenvalue, equal to $\max_q \varphi(q)$
-- statement:
--   Let $N \ge 1$. For each row $i$ let $S_i$ be a set of parameters, and let $a_{ij}(q_i)$ be real numbers for $q_i \in S_i$; for a joint parameter $q = (q_1,\dots,q_N) \in S = S_1\times\dots\times S_N$ write $A(q) = (a_{ij}(q_i))$ and let $\varphi(q)$ be the Perron root of $A(q)$, its characteristic root of largest absolute value. Assume the conditions (10.3):
--
--   1. for every $y \in \mathbb R^N$ the maximum of $\sum_j a_{ij}(q_i) y_j$ over $q_i \in S_i$ is attained, for each $i$;
--   2. $0 < a_{ij}(q) \le m < \infty$ for all $q \in S$ and all $i, j$;
--   3. $\varphi(q)$ attains its maximum on $S$.
--
--   Then there is exactly one constant $\lambda > 0$ for which the homogeneous system
--   $$\lambda y_i = \max_{q} \sum_{j=1}^N a_{ij}(q)\, y_j, \qquad i = 1, \dots, N,$$
--   has a positive solution $y_i > 0$ for all $i$. This solution is unique up to a positive multiplicative constant, and
--   $$\lambda = \max_{q \in S} \varphi(q).$$
--
--   The theorem is a nonlinear Perron–Frobenius theorem: the growth rate of the optimally controlled multiplicative process equals the largest Perron root among the admissible matrices. It is the basis of the asymptotic result, Theorem 3.
--
--   **Formalization Note** The Perron root is the spectral radius of $A(q)$ as a complex matrix. The maximization is row by row (Bellman, § 3). Uniqueness of $\lambda$ is among positive constants admitting a positive solution.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter XI, Theorem 2, p. 329 (with Eqs. (10.2)-(10.3), p. 329)

import Mathlib
import Definitions.Def_BellmanDP_Markovian_Discrete

namespace BellmanDP.Markovian

/-- Bellman, *Dynamic Programming*, Ch. XI, Theorem 2, p. 329. Under the conditions (10.3a)–(c),
the homogeneous system `λ y_i = Max_q Σ_j a_ij(q) y_j` (10.2) has a positive solution `y` for
exactly one positive constant `λ`; the positive solution is unique up to a positive multiplicative
constant; and `λ = Max_{q ∈ S} φ(q)`, `φ(q)` the Perron root of `A(q)`. -/
theorem perron_eigen_exists_unique {N : ℕ} (hN : 0 < N) {Q : Fin N → Type*}
    (a : (i : Fin N) → Q i → Fin N → ℝ) (S : (i : Fin N) → Set (Q i)) (m : ℝ)
    (h : MarkovHyp a S m) :
    ∃ (lam : ℝ) (y : Fin N → ℝ), 0 < lam ∧ (∀ i, 0 < y i) ∧ IsMaxEigenpair a S lam y ∧
      (∀ (μ : ℝ) (z : Fin N → ℝ), 0 < μ → (∀ i, 0 < z i) → IsMaxEigenpair a S μ z →
        μ = lam ∧ ∃ κ : ℝ, 0 < κ ∧ z = κ • y) ∧
      IsGreatest ((fun q => perronRoot (matOf a q)) '' Set.pi Set.univ S) lam := by sorry

end BellmanDP.Markovian
