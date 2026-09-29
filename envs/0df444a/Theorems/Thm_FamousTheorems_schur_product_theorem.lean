-- Prove2me | Theorems.Thm_FamousTheorems_schur_product_theorem
-- name    : FamousTheorems.schur_product_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:08.5566+00:00
-- url     : https://prove2.me/theorems/01aa4003-3dfc-4822-9d5f-a3e52c0ed966
-- title:
--   The Schur product theorem
-- statement:
--   **The Schur product theorem.** Let $A$ and $B$ be positive semidefinite matrices over $\mathbb R$ or $\mathbb C$. Then their Hadamard (entrywise) product $A\circ B$, with entries $(A\circ B)_{ij}=A_{ij}B_{ij}$, is positive semidefinite.
--
--   The theorem shows that positive semidefinite kernels are closed under pointwise products. It is used in the theory of reproducing kernels and machine learning (products of kernels are kernels), in matrix analysis, and in the study of positive definite functions. For example, it shows that the entrywise exponential of a positive semidefinite matrix is positive semidefinite.
--
--   **Formalization note.** Mathlib's `Matrix.PosSemidef.hadamard`, over any `RCLike` field `𝕜` (ℝ or ℂ) with the complex order opened. `Matrix.PosSemidef` means Hermitian with $x^*Ax\ge0$ for all $x$, and `A.hadamard B` is the entrywise product.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Matrix.PosSemidef.hadamard`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped ComplexOrder

theorem schur_product_theorem {𝕜 ι : Type*} [RCLike 𝕜] {A B : Matrix ι ι 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A.hadamard B).PosSemidef := by sorry

end FamousTheorems
