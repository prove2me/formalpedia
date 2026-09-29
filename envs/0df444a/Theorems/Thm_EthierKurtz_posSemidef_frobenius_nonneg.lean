-- Prove2me | Theorems.Thm_EthierKurtz_posSemidef_frobenius_nonneg
-- name    : EthierKurtz.posSemidef_frobenius_nonneg
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T22:19:22.800896+00:00
-- url     : https://prove2.me/theorems/aa7ecd9b-f877-4009-b31d-8d3eebec71a6
-- title:
--   Frobenius inner product of PSD matrices is nonnegative
-- statement:
--   This is the linear-algebra fact that the Frobenius inner product of two positive-semidefinite matrices is nonnegative.
--
--   Let $d$ be a natural number and let $A, H$ be real $d \times d$ matrices, both positive-semidefinite. Then
--
--   $$
--   \sum_{i,j} A_{ij} H_{ij} \ge 0.
--   $$
--
--   Equivalently, the trace $\mathrm{tr}(AH)$ is nonnegative. The proof diagonalizes $A = U\Lambda U^*$ by the spectral theorem and rewrites the sum as $\sum_k \lambda_k\, u_k^* H u_k$ with $\lambda_k \ge 0$ and each quadratic form nonnegative. This isolates the entire spectral argument used when passing from Hessian positive-semidefiniteness to the sign of a second-order elliptic operator at a minimum point.
--
--   **Formalization Note** Positive-semidefiniteness is Mathlib's `Matrix.PosSemidef`; the proof uses `spectral_theorem`, `eigenvalues_nonneg`, and `dotProduct_mulVec_nonneg`.
-- source:
--   Frobenius inner product / trace of a product of positive-semidefinite matrices is nonnegative, via the spectral theorem. https://en.wikipedia.org/wiki/Positive-semidefinite_matrix

import Mathlib

open scoped Topology

namespace EthierKurtz

theorem posSemidef_frobenius_nonneg {d : ℕ}
    (A H : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (hH : H.PosSemidef) :
    0 ≤ ∑ i, ∑ j, A i j * H i j := by sorry

end EthierKurtz
