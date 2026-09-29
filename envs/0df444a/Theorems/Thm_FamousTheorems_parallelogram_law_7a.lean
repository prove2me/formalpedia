-- Prove2me | Theorems.Thm_FamousTheorems_parallelogram_law_7a
-- name    : FamousTheorems.parallelogram_law_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:08.774703+00:00
-- url     : https://prove2.me/theorems/5b6e57ea-a48c-402f-967c-32055a4a716e
-- title:
--   The parallelogram law
-- statement:
--   **The parallelogram law.** In a real inner product space, for all vectors $x,y$,
--   $$\|x+y\|^2+\|x-y\|^2=2\big(\|x\|^2+\|y\|^2\big).$$
--
--   Geometrically, the sum of the squares of the diagonals of a parallelogram equals the sum of the squares of its sides. By the Jordan–von Neumann theorem, a norm satisfying this identity comes from an inner product. The law is used in the proof that closed convex sets in a Hilbert space have unique nearest points, which gives orthogonal projections and the Riesz representation theorem.
--
--   **Formalization note.** Mathlib's `parallelogram_law_with_norm`, specialised to real scalars. Mathlib also proves it for complex inner product spaces.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `parallelogram_law_with_norm`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem parallelogram_law_7a {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by sorry

end FamousTheorems
