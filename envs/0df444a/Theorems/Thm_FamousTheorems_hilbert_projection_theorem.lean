-- Prove2me | Theorems.Thm_FamousTheorems_hilbert_projection_theorem
-- name    : FamousTheorems.hilbert_projection_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:08.82679+00:00
-- url     : https://prove2.me/theorems/c72302b4-9a6a-4b87-b35d-620d7a993f4a
-- title:
--   The Hilbert projection theorem
-- statement:
--   **The Hilbert projection theorem.** Let $K$ be a nonempty complete convex subset of a real inner product space (e.g. a closed convex subset of a Hilbert space). For every point $u$ there is $v\in K$ minimising the distance to $u$:
--   $$\|u-v\|=\inf_{w\in K}\|u-w\| .$$
--
--   The minimiser is unique and is characterised by a variational inequality. This is the basis of orthogonal projections, the decomposition $H=M\oplus M^\perp$, the Riesz representation theorem, and least-squares approximation.
--
--   **Formalization note.** Mathlib's `exists_norm_eq_iInf_of_complete_convex` (existence only; uniqueness is a separate lemma).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `exists_norm_eq_iInf_of_complete_convex`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hilbert_projection_theorem {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {K : Set F} (hne : K.Nonempty)
    (hc : IsComplete K) (hK : Convex ℝ K) (u : F) : ∃ v ∈ K, ‖u - v‖ = ⨅ w : K, ‖u - w‖ := by sorry

end FamousTheorems
