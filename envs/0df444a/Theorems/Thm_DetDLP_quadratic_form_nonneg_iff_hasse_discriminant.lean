-- Prove2me | Theorems.Thm_DetDLP_quadratic_form_nonneg_iff_hasse_discriminant
-- name    : DetDLP.quadratic_form_nonneg_iff_hasse_discriminant
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T14:28:48.018805+00:00
-- url     : https://prove2.me/theorems/9af28308-19fd-42e9-be37-77c55f6ffcf3
-- title:
--   Binary Quadratic-Form Positive-Semidefiniteness Equivalence for Hasse's Discriminant Bound
-- statement:
--   Proves the pure algebraic characterization of Hasse's elliptic-curve point-count discriminant bound $(N - (p + 1))^2 \le 4p$ via the positive-semidefiniteness of the binary quadratic form $Q(m, n) = m^2 p - m n (p + 1 - N) + n^2$ on $\mathbb{Z} \times \mathbb{Z}$:
--
--   1. **Completing-the-square identity:** for all $p, N, m, n \in \mathbb{Z}$, $$4p(m^2 p - m n (p + 1 - N) + n^2) = (2pm - (p + 1 - N)n)^2 + (4p - (N - (p + 1))^2)n^2;$$
--   2. **Exact equivalence (`↔`):** for all $p, N \in \mathbb{Z}$ with $p > 0$, $$(\forall m, n \in \mathbb{Z},\; m^2 p - m n (p + 1 - N) + n^2 \ge 0) \iff (N - (p + 1))^2 \le 4p.$$
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.2 Proof of Theorem 3.1 (Hasse's bound, pp. 12–13)

import Mathlib

set_option autoImplicit false

namespace DetDLP

/-- Pure algebraic characterization of Hasse's elliptic-curve discriminant bound via the
positive-semidefiniteness of the binary quadratic form `m^2 p - m n (p + 1 - N) + n^2`:
(1) Explicit completing-the-square identity:
    `4 p (m^2 p - m n (p + 1 - N) + n^2) = (2 p m - (p + 1 - N) n)^2 + (4 p - (N - (p + 1))^2) n^2`.
(2) Exact necessary and sufficient condition (`↔`): for any `p > 0` and `N : ℤ`,
    `(∀ m n : ℤ, 0 ≤ m^2 p - m n (p + 1 - N) + n^2) ↔ (N - (p + 1))^2 ≤ 4 p`. -/
theorem quadratic_form_nonneg_iff_hasse_discriminant :
    (∀ (p N m n : ℤ),
      4 * p * (m ^ 2 * p - m * n * (p + 1 - N) + n ^ 2) =
        (2 * p * m - (p + 1 - N) * n) ^ 2 + (4 * p - (N - (p + 1)) ^ 2) * n ^ 2) ∧
    (∀ (p N : ℤ), 0 < p →
      ((∀ m n : ℤ, 0 ≤ m ^ 2 * p - m * n * (p + 1 - N) + n ^ 2) ↔
        (N - (p + 1)) ^ 2 ≤ 4 * p)) := by
  sorry

end DetDLP
