-- Prove2me | Theorems.Thm_FamousTheorems_eigenvalue_mem_ball
-- name    : FamousTheorems.eigenvalue_mem_ball
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:55.317882+00:00
-- url     : https://prove2.me/theorems/a20191c3-5607-4d61-9570-1da2464e3ad0
-- title:
--   The Gershgorin circle theorem
-- statement:
--   **The Gershgorin circle theorem.** Every eigenvalue of a square matrix lies in one of the discs centred at a diagonal entry $a_{ii}$ with radius the sum of the absolute values of the other entries in that row. Eigenvalues — roots of a degree-$n$ polynomial, generally uncomputable in closed form — are localised by reading off the matrix entries directly. The proof is a one-line argument: take a largest-modulus coordinate of an eigenvector and compare terms. It gives instant invertibility criteria (strictly diagonally dominant matrices are nonsingular, since $0$ lies in no disc) and underpins numerical eigenvalue estimation and stability analysis. **Formalization note.** The discs are `Metric.ball` in the scalar field with the stated radii. The result is Mathlib's `eigenvalue_mem_ball`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem eigenvalue_mem_ball :
    ∀ {K : Type u_1} {n : Type u_2} [inst : NormedField K] [inst_1 : Fintype n] 
    [inst_2 : DecidableEq n] {A : Matrix n n K} {μ : K}, 
    Module.End.HasEigenvalue (Matrix.toLin' A) μ → ∃ k, μ ∈ Metric.closedBall (A k k) (∑ j ∈ Finset.univ.erase k, ‖A k j‖) := by sorry

end FamousTheorems
