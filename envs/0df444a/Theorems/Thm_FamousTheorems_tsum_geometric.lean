-- Prove2me | Theorems.Thm_FamousTheorems_tsum_geometric
-- name    : FamousTheorems.tsum_geometric
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T07:14:54.917652+00:00
-- url     : https://prove2.me/theorems/bb16fe6b-9598-464a-b91c-f6bc21b96d5d
-- title:
--   Sum of a geometric series in a normed division ring
-- statement:
--   **The geometric series** in a complete normed division ring.
--
--   If $\lVert \xi \rVert < 1$ then
--   $$\sum_{n=0}^{\infty} \xi^n = (1-\xi)^{-1}.$$
--
--   The series converges absolutely by comparison with $\sum \lVert\xi\rVert^n$, and its sum
--   inverts $1-\xi$. Commutativity is not needed — every term is a power of the single element
--   $\xi$ — so the statement covers quaternions and, in the operator-algebra version, bounded
--   linear operators of norm less than one.
--
--   That generalization is the Neumann series, and it is the reason the invertible elements of a
--   Banach algebra form an open set: perturbing an invertible $a$ by less than
--   $\lVert a^{-1}\rVert^{-1}$ keeps it invertible, with the inverse given by this series. It is
--   also the analytic engine behind the resolvent being holomorphic and behind convergence proofs
--   for iterative linear solvers.
--
--   **Formalization note.** `∑'` is the unconditional sum over `ℕ`, which agrees with the limit
--   of partial sums here because convergence is absolute. The result is Mathlib's
--   `tsum_geometric_of_norm_lt_one`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests (docs/undergrad.yaml, docs/overview.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v

open Filter Set Topology DirectSum

theorem tsum_geometric {K : Type*} [NormedDivisionRing K] [CompleteSpace K] {ξ : K}
    (h : ‖ξ‖ < 1) : ∑' n : ℕ, ξ ^ n = (1 - ξ)⁻¹ := by sorry

end FamousTheorems
