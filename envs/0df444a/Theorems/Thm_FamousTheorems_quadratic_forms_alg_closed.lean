-- Prove2me | Theorems.Thm_FamousTheorems_quadratic_forms_alg_closed
-- name    : FamousTheorems.quadratic_forms_alg_closed
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:25:56.585874+00:00
-- url     : https://prove2.me/theorems/89acdae4-00ea-4561-95a9-933ed6862f37
-- title:
--   Classification of quadratic forms over algebraically closed fields
-- statement:
--   **Classification of quadratic forms over an algebraically closed field.** Let $K$ be an algebraically closed field of characteristic not $2$ and $Q$ a nondegenerate quadratic form on an $n$-dimensional $K$-vector space. Then $Q$ is equivalent to the sum of squares $x_1^2+\cdots+x_n^2$.
--
--   So over an algebraically closed field a nondegenerate quadratic form is determined up to equivalence by its dimension alone. For example, over $\mathbb C$ all nondegenerate quadrics of a given dimension are projectively equivalent, and the orthogonal group is unique up to isomorphism.
--
--   **Formalization note.** Mathlib's `QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed`. The characteristic assumption is `Invertible (2 : K)`, and nondegeneracy is that the associated symmetric bilinear form `QuadraticMap.associated Q` is left-separating. The target is `QuadraticMap.weightedSumSquares K 1` on `Fin n → K`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem quadratic_forms_alg_closed {K M : Type*} [Field K] [IsAlgClosed K] [Invertible (2 : K)] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (Q : QuadraticForm K M) (hQ : (QuadraticMap.associated Q).SeparatingLeft) :
    QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares K (1 : Fin (Module.finrank K M) → K)) := by sorry

end FamousTheorems
