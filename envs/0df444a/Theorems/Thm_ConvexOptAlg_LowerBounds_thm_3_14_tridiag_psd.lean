-- Prove2me | Theorems.Thm_ConvexOptAlg_LowerBounds_thm_3_14_tridiag_psd
-- name    : ConvexOptAlg.LowerBounds.thm_3_14_tridiag_psd
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:43:30.367422+00:00
-- url     : https://prove2.me/theorems/cbf08400-82bd-4379-a5fe-37837565b377
-- title:
--   Proof of Theorem 3.14, p. 282 — A_k is symmetric and 0 ⪯ A_k ⪯ 4Iₙ via the quadratic-form identity
-- statement:
--   Let $1\le k\le n$ and let $A_k\in\mathbb R^{n\times n}$ be the tridiagonal matrix with $2$ on the first $k$ diagonal entries, $-1$ on the adjacent off-diagonal entries inside the leading $k\times k$ block, and $0$ elsewhere. Then $A_k$ is symmetric and for every $x\in\mathbb R^n$
--   $$x^\top A_kx=2\sum_{i=1}^{k}x(i)^2-2\sum_{i=1}^{k-1}x(i)x(i+1)=x(1)^2+x(k)^2+\sum_{i=1}^{k-1}\bigl(x(i)-x(i+1)\bigr)^2 ,$$
--   and $0\le x^\top A_kx\le 4\|x\|^2$, that is $0\preceq A_k\preceq 4I_n$.
--
--   The bound $A_k\preceq4I_n$ is what makes the hard instance of Theorem 3.14 $\beta$-smooth, and $A_k\succeq0$ makes it convex.
--
--   **Formalization Note** $x(i)$ is the book's 1-based coordinate (`coord x i`). The case $k=0$ is excluded because the identity refers to $x(1)$ and $x(k)$.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.14, p. 282

import Mathlib
import Definitions.Def_ConvexOptAlg_LowerBounds_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.LowerBounds

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 3.14, p. 282: for `1 ≤ k ≤ n` the tridiagonal
matrix `A_k` is symmetric and satisfies `0 ⪯ A_k ⪯ 4Iₙ`, because
`xᵀA_k x = 2 Σ_{i=1}^{k} x(i)² − 2 Σ_{i=1}^{k−1} x(i)x(i+1) = x(1)² + x(k)² + Σ_{i=1}^{k−1} (x(i) − x(i+1))²`.
Coordinates `x(i)` are the book's 1-based ones (`coord x i` is the `Fin n` entry `i − 1`). -/
theorem thm_3_14_tridiag_psd (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (tridiag n k).IsSymm ∧
      ∀ x : EuclideanSpace ℝ (Fin n),
        quadForm (tridiag n k) x =
            2 * ∑ i ∈ Finset.Icc 1 k, coord x i ^ 2
              - 2 * ∑ i ∈ Finset.Icc 1 (k - 1), coord x i * coord x (i + 1) ∧
          2 * ∑ i ∈ Finset.Icc 1 k, coord x i ^ 2
              - 2 * ∑ i ∈ Finset.Icc 1 (k - 1), coord x i * coord x (i + 1) =
            coord x 1 ^ 2 + coord x k ^ 2
              + ∑ i ∈ Finset.Icc 1 (k - 1), (coord x i - coord x (i + 1)) ^ 2 ∧
          0 ≤ quadForm (tridiag n k) x ∧ quadForm (tridiag n k) x ≤ 4 * ‖x‖ ^ 2 := by sorry

end ConvexOptAlg.LowerBounds
