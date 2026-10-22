-- Prove2me | Theorems.Thm_FlowsNetworks_Feasibility_matrix_row_column_bounds
-- name    : FlowsNetworks.Feasibility.matrix_row_column_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:37.564032+00:00
-- url     : https://prove2.me/theorems/7a63708f-89a5-436c-b929-ab88acbcd748
-- title:
--   Chapter II, Corollary 2.3 — nonnegative bounded matrices with row and column sums between limits
-- statement:
--   Let $m, n$ be natural numbers and let $0 \le a_i \le a'_i$ ($i = 1, \dots, m$), $0 \le b_j \le b'_j$ ($j = 1, \dots, n$) and $c_{ij} \ge 0$ be given real constants. Suppose there are real $m \times n$ matrices $(f^1_{ij})$ and $(f^2_{ij})$ with
--   $$a_i \le \sum_j f^1_{ij}, \quad \sum_i f^1_{ij} \le b'_j, \quad 0 \le f^1_{ij} \le c_{ij},$$
--   $$\sum_j f^2_{ij} \le a'_i, \quad b_j \le \sum_i f^2_{ij}, \quad 0 \le f^2_{ij} \le c_{ij},$$
--   for all $i, j$. Then there is a real $m \times n$ matrix $(f_{ij})$ with
--   $$a_i \le \sum_j f_{ij} \le a'_i, \quad b_j \le \sum_i f_{ij} \le b'_j, \quad 0 \le f_{ij} \le c_{ij}$$
--   for all $i, j$.
--
--   A nonnegative matrix with entrywise upper bounds whose row sums and column sums lie between prescribed limits therefore exists as soon as the lower row limits can be met together with the upper column limits, and the upper row limits together with the lower column limits.
--
--   **Formalization Note** Rows and columns are indexed by `Fin m` and `Fin n` (from $0$) instead of $1, \dots, m$ and $1, \dots, n$; $m = 0$ or $n = 0$ is allowed. The two hypotheses are separate existence statements, as on the page.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 23, Corollary 2.3

import Mathlib

namespace FlowsNetworks.Feasibility

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Corollary 2.3 (p. 23). Let `0 ≤ a_i ≤ a'_i`
(`i = 1, …, m`), `0 ≤ b_j ≤ b'_j` (`j = 1, …, n`) and `c_ij ≥ 0` be real constants. If there are
real `m × n` matrices `f¹`, `f²` with (2.9) `a_i ≤ ∑_j f¹_ij`, `∑_i f¹_ij ≤ b'_j`, `0 ≤ f¹_ij ≤ c_ij`
and (2.10) `∑_j f²_ij ≤ a'_i`, `b_j ≤ ∑_i f²_ij`, `0 ≤ f²_ij ≤ c_ij`, then there is a real matrix
`f` with (2.11) `a_i ≤ ∑_j f_ij ≤ a'_i`, `b_j ≤ ∑_i f_ij ≤ b'_j`, `0 ≤ f_ij ≤ c_ij`. Indices run
over `Fin m` and `Fin n` (0-based) instead of `1, …, m` and `1, …, n`. -/
theorem matrix_row_column_bounds (m n : ℕ) (a a' : Fin m → ℝ) (b b' : Fin n → ℝ)
    (c : Matrix (Fin m) (Fin n) ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ a' i) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ b' j)
    (hc : ∀ i j, 0 ≤ c i j)
    (h1 : ∃ f₁ : Matrix (Fin m) (Fin n) ℝ,
      (∀ i, a i ≤ ∑ j, f₁ i j) ∧ (∀ j, ∑ i, f₁ i j ≤ b' j) ∧
        ∀ i j, 0 ≤ f₁ i j ∧ f₁ i j ≤ c i j)
    (h2 : ∃ f₂ : Matrix (Fin m) (Fin n) ℝ,
      (∀ i, ∑ j, f₂ i j ≤ a' i) ∧ (∀ j, b j ≤ ∑ i, f₂ i j) ∧
        ∀ i j, 0 ≤ f₂ i j ∧ f₂ i j ≤ c i j) :
    ∃ f : Matrix (Fin m) (Fin n) ℝ,
      (∀ i, a i ≤ ∑ j, f i j ∧ ∑ j, f i j ≤ a' i) ∧
        (∀ j, b j ≤ ∑ i, f i j ∧ ∑ i, f i j ≤ b' j) ∧
        ∀ i j, 0 ≤ f i j ∧ f i j ≤ c i j := by sorry

end FlowsNetworks.Feasibility
