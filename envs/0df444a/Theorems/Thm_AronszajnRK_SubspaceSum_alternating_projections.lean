-- Prove2me | Theorems.Thm_AronszajnRK_SubspaceSum_alternating_projections
-- name    : AronszajnRK.SubspaceSum.alternating_projections
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:12:48.231399+00:00
-- url     : https://prove2.me/theorems/503c5bb8-ffec-4b35-888a-a96509d83c38
-- title:
--   §12, p. 376 — alternating projections converge to the intersection projection
-- statement:
--   Let $F_1,F_2$ be closed subspaces of a complex Hilbert space. Write $P_1,P_2$ for their orthogonal projections and $P_0$ for the projection onto $F_1\cap F_2$. For every vector $f$,
--
--   $$
--   (P_2P_1)^m f\longrightarrow P_0f\qquad(m\to\infty).
--   $$
--
--   This identifies the first limiting term in the finite projection identity.
--
--   **Formalization Note** The convergence is in the norm of each vector, also called strong operator convergence. No convergence in operator norm is asserted.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 376, §12, paragraph after Eq. (4)

import Mathlib
import Definitions.Def_AronszajnRK_SubspaceSum_intersectionProjection

namespace AronszajnRK.SubspaceSum

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950),
§12, p. 376 (PDF p. 40). The alternating projection powers converge strongly to P₀. -/
theorem alternating_projections {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (F₁ F₂ : ClosedSubmodule ℂ E) (f : E) :
    let P₁ : E →L[ℂ] E := (F₁ : Submodule ℂ E).starProjection
    let P₂ : E →L[ℂ] E := (F₂ : Submodule ℂ E).starProjection
    Filter.Tendsto (fun m : ℕ => ((P₂ * P₁) ^ m) f) Filter.atTop
      (nhds (intersectionProjection F₁ F₂ f)) := by sorry

end AronszajnRK.SubspaceSum
