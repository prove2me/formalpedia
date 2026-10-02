-- Prove2me | Theorems.Thm_AppliedComb_Recurrence_principal
-- name    : AppliedComb.Recurrence.principal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:17:09.763189+00:00
-- url     : https://prove2.me/theorems/e4caca93-ef7b-482a-b6df-681ac292d97a
-- title:
--   Theorem 9.18 — the Principal Theorem: the solutions of p(A)f = 0 form a k-dimensional space
-- statement:
--   Let $V$ be the real vector space of all functions $f : \mathbb{Z} \to \mathbb{R}$ and $A$ the advancement operator, $Af(n) = f(n+1)$. Let $k$ be a positive integer and let $c_0, c_1, \dots, c_k$ be real constants with $c_0 \neq 0$ and $c_k \neq 0$. Then the set $W$ of all solutions of the homogeneous linear equation
--
--   $$(c_0 A^k + c_1 A^{k-1} + c_2 A^{k-2} + \cdots + c_k) f = 0 \qquad (9.5.1)$$
--
--   is a $k$-dimensional subspace of $V$:
--
--   $$\dim_{\mathbb{R}} W = k.$$
--
--   This is the basic theorem about constant-coefficient linear recurrence equations: solving such an equation amounts to finding a basis of $W$, and every solution is a linear combination of $k$ basis functions.
--
--   **Formalization Note.** $W$ is `solutionSpace k c`, the kernel of `opPoly k c` on `ℤ → ℝ`, with `c 0` $= c_0$ and `c (Fin.last k)` $= c_k$. Dimension is `Module.rank` (a cardinal), so the statement also asserts that $W$ is finite-dimensional. On $\mathbb{Z}$-indexed functions the hypothesis $c_k \neq 0$ is essential (for $c_k = 0$ the dimension drops); this is not Mathlib's `LinearRecurrence.solSpace_rank`, which concerns $\mathbb{N}$-indexed sequences and a monic recurrence.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 199, Theorem 9.18

import Mathlib
import Definitions.Def_AppliedComb_Recurrence_advance

namespace AppliedComb.Recurrence

/-- Keller–Trotter, Theorem 9.18 (p. 199), the Principal Theorem. Let `k` be a positive integer
and let `c₀, c₁, …, c_k` be real constants with `c₀ ≠ 0` and `c_k ≠ 0`. Then the set `W` of all
solutions `f : ℤ → ℝ` of the homogeneous equation `(c₀ A^k + c₁ A^(k-1) + ⋯ + c_k) f = 0` (9.5.1)
is a `k`-dimensional subspace of `V = (ℤ → ℝ)`: its dimension (`Module.rank`, a cardinal, so
an infinite-dimensional `W` would not satisfy the statement) equals `k`. -/
theorem principal (k : ℕ) (hk : 0 < k) (c : Fin (k + 1) → ℝ) (hc0 : c 0 ≠ 0)
    (hck : c (Fin.last k) ≠ 0) :
    Module.rank ℝ (solutionSpace k c) = k := by sorry

end AppliedComb.Recurrence
