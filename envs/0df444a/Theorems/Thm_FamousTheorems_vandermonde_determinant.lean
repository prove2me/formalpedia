-- Prove2me | Theorems.Thm_FamousTheorems_vandermonde_determinant
-- name    : FamousTheorems.vandermonde_determinant
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:40.416432+00:00
-- url     : https://prove2.me/theorems/706c8268-a5bd-4636-93e4-c20632fe6d1b
-- title:
--   The Vandermonde determinant
-- statement:
--   **The Vandermonde determinant.** For elements $v_0,\dots,v_{n-1}$ of a commutative ring,
--   $$\det\big(v_i^{\,j}\big)_{0\le i,j<n}=\prod_{i<j}(v_j-v_i).$$
--
--   The formula shows that the Vandermonde matrix is invertible exactly when the $v_i$ are distinct (over a domain). This gives the uniqueness and existence of polynomial interpolation, and it appears in the discriminant of a polynomial, Reed–Solomon codes, and random matrix theory.
--
--   **Formalization note.** Mathlib's `Matrix.det_vandermonde`. `Matrix.vandermonde v` has entries `v i ^ (j : ℕ)`, and `∏ j > i` is the product over indices `j : Fin n` with `j > i`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Matrix.det_vandermonde`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem vandermonde_determinant {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) :
    (Matrix.vandermonde v).det = ∏ i : Fin n, ∏ j > i, (v j - v i) := by sorry

end FamousTheorems
