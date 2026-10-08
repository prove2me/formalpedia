-- Prove2me | Theorems.Thm_CompOT_Barycenter_kl_matrix_conjugate
-- name    : CompOT.Barycenter.kl_matrix_conjugate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:53.077992+00:00
-- url     : https://prove2.me/theorems/f3bad7ff-12a1-41cf-8c5e-df66e731d080
-- title:
--   (9.22), p. 530 — matrix KL conjugate
-- statement:
--   Let $K$ be a finite matrix with strictly positive entries, and let $U$ be any real matrix of the same shape. For nonnegative matrices $P$, define $\mathrm{KL}(P\mid K)$ by summing the scalar generalized KL terms. Its convex conjugate is
--   $$\max_{P\ge0}\{\langle U,P\rangle-\mathrm{KL}(P\mid K)\}=\sum_{i,j}K_{ij}(e^{U_{ij}}-1).$$
--   The maximizing matrix has entries $P_{ij}=K_{ij}e^{U_{ij}}$.
--
--   This is the separable transformation that turns the KL projection problem into the exponential dual objective.
--
--   **Formalization Note** The theorem states both the universal upper bound and attainment, so its use of “max” is literal even when an index type is empty.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), (9.22), proof of Proposition 9.1, p. 530

import Mathlib
import Definitions.Def_CompOT_Barycenter_Defs

namespace CompOT.Barycenter

/-- The separable matrix KL conjugate (9.22), p. 530. -/
theorem kl_matrix_conjugate {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (U K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j) :
    (∀ P : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ P i j) →
      (∑ i, ∑ j, U i j * P i j) - klMatrix P K ≤
        ∑ i, ∑ j, K i j * (Real.exp (U i j) - 1)) ∧
    (∑ i, ∑ j, U i j * (K i j * Real.exp (U i j))) -
      klMatrix (fun i j => K i j * Real.exp (U i j)) K =
        ∑ i, ∑ j, K i j * (Real.exp (U i j) - 1) := by sorry

end CompOT.Barycenter
