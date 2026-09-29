-- Prove2me | Theorems.Thm_AlonMilman_Diameter_lambda0_eq_zero_lt_lambda1
-- name    : AlonMilman.Diameter.lambda0_eq_zero_lt_lambda1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:25:41.703808+00:00
-- url     : https://prove2.me/theorems/be40781d-abb7-47d9-91d1-ce835b00c356
-- title:
--   Section 2, p. 76 — $0 = \lambda_0 < \lambda_1$ for a connected graph
-- statement:
--   Let $G = (V, E)$ be a connected finite simple graph on $n \ge 2$ vertices with Laplacian $Q = \operatorname{diag}(d(v)) - A_G$, and let $\lambda_0 \le \lambda_1 \le \cdots \le \lambda_{n-1}$ be the eigenvalues of $Q$ with multiplicity. Then
--   $$
--   0 = \lambda_0 < \lambda_1 = \lambda_1(G).
--   $$
--
--   The smallest eigenvalue of the Laplacian of a connected graph is $0$ (with the constant eigenvectors) and it is simple, so the algebraic connectivity is strictly positive. This is what makes the divisions by $\lambda_1$ in the diameter bound meaningful.
--
--   **Formalization Note** $\lambda_0$ is `eigenvalues₀` at index $n-1$ (the list is decreasing) and $\lambda_1$ is the mission's `lambda1`, which is `eigenvalues₀` at index $n-2$.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 76, Section 2 (unnumbered: 'Let 0 = λ₀ < λ₁ = λ₁(G) ≤ λ₂ ≤ ··· ≤ λ_{n−1} be the eigenvalues of Q')

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1

namespace AlonMilman.Diameter

theorem lambda0_eq_zero_lt_lambda1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 1, by omega⟩ = 0 ∧
      0 < lambda1 G := by sorry

end AlonMilman.Diameter
