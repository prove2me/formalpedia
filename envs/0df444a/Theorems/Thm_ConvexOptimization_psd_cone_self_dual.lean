-- Prove2me | Theorems.Thm_ConvexOptimization_psd_cone_self_dual
-- name    : ConvexOptimization.psd_cone_self_dual
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-11T21:39:37.370949+00:00
-- url     : https://prove2.me/theorems/b045a31d-e801-4dc0-a0ab-0d5141890bc0
-- title:
--   The PSD cone is self-dual
-- statement:
--   **The positive semidefinite cone is self-dual.**
--
--   Equip the space of symmetric real $n \times n$ matrices with the trace inner product $\langle A, B\rangle = \operatorname{tr}(AB)$. Let $A$ be symmetric. Then
--
--   $$\bigl(\operatorname{tr}(AB) \ge 0 \ \text{ for every } B \succeq 0\bigr) \qquad\Longleftrightarrow\qquad A \succeq 0 .$$
--
--   In the language of dual cones, $\mathbb{S}^n_{+}{}^{*} = \mathbb{S}^n_{+}$: the cone of positive semidefinite matrices coincides with its own dual.
--
--   Self-duality is why semidefinite programming is dual to semidefinite programming, with the same cone appearing on both sides — the same phenomenon that makes linear programming dual to linear programming through self-duality of the nonnegative orthant. The forward direction is also the standard route to certifying $A \succeq 0$ by testing against rank-one matrices $B = vv^{T}$, for which $\operatorname{tr}(AB) = v^{T}Av$.
--
--   **Formalization Note** Matrices are `Matrix (Fin n) (Fin n) ℝ`, symmetry is `A.IsSymm`, and the trace pairing is written `(A * B).trace`; the statement is an iff, so both the duality inclusion and its converse are asserted. Source: B&V §2.6.1, example 2.24, p. 52.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 52, §2.6.1 example 2.24 (the positive semidefinite cone is self-dual)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.psd_cone_self_dual {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    (∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef → 0 ≤ (A * B).trace) ↔
      A.PosSemidef := by
  sorry
