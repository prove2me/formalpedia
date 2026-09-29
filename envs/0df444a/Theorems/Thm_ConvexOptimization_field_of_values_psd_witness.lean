-- Prove2me | Theorems.Thm_ConvexOptimization_field_of_values_psd_witness
-- name    : ConvexOptimization.field_of_values_psd_witness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T16:04:47.621857+00:00
-- url     : https://prove2.me/theorems/134f86d9-5023-4830-8f7d-801578d1d354
-- title:
--   Dines's theorem: vector witness for PSD averages of two quadratic forms
-- statement:
--   **Hidden convexity of the joint range of two quadratic forms:** any value attained by a positive semidefinite matrix is attained by a rank-one one.
--
--   Let $A, B$ be symmetric $n \times n$ real matrices and let $X$ be positive semidefinite. Then there exists a single vector $x \in \mathbb{R}^n$ with
--
--   $$x^{T} A x \;=\; \operatorname{tr}(AX), \qquad x^{T} B x \;=\; \operatorname{tr}(BX).$$
--
--   Equivalently, the set $\{(x^{T}Ax,\, x^{T}Bx) : x \in \mathbb{R}^n\} \subseteq \mathbb{R}^2$ — the joint range of the pair — already contains everything the larger set $\{(\operatorname{tr}(AX), \operatorname{tr}(BX)) : X \succeq 0\}$ contains, so the semidefinite relaxation of a *pair* of quadratic forms is exact.
--
--   This is the precise reason the S-procedure is lossless: the proof relaxes a pair of quadratic inequalities to a semidefinite program, and this statement converts a matrix solution of the relaxation back into a genuine vector. It is a two-form phenomenon — for three or more quadratic forms the analogous statement fails, and the S-procedure acquires a gap.
--
--   **Formalization Note** The conclusion is an existential over `x : Fin n → ℝ` with both quadratic values written using `⬝ᵥ` and `Matrix.mulVec`, and `X.PosSemidef` in Mathlib already carries Hermitian-ness. The book proves it by induction on the rank of $X$. Source: B&V §B.3, p. 656, eq. (B.8).
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 656, §B.3 eq. (B.8) (the set W(A,B); every value attained by a PSD matrix on a pair of quadratic forms is attained by a rank-one one)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.field_of_values_psd_witness {nn : ℕ}
    (A B : Matrix (Fin nn) (Fin nn) ℝ) (hA : A.IsSymm) (hB : B.IsSymm)
    (X : Matrix (Fin nn) (Fin nn) ℝ) (hX : X.PosSemidef) :
    ∃ x : Fin nn → ℝ,
      x ⬝ᵥ A.mulVec x = (A * X).trace ∧ x ⬝ᵥ B.mulVec x = (B * X).trace := by
  sorry
