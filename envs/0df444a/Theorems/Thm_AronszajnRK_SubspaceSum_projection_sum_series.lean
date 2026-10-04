-- Prove2me | Theorems.Thm_AronszajnRK_SubspaceSum_projection_sum_series
-- name    : AronszajnRK.SubspaceSum.projection_sum_series
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:13:20.038863+00:00
-- url     : https://prove2.me/theorems/5a66dac1-b435-4ac6-86f0-2a4fb152e9bf
-- title:
--   §12, Eq. (7) — strong series for the projection onto a closed sum
-- statement:
--   Let $F_1,F_2$ be closed subspaces of a complex Hilbert space. Write $P_i$ for the orthogonal projection onto $F_i$, $P_0$ for the projection onto $F_1\cap F_2$, and $P$ for the projection onto $\overline{F_1+F_2}$. Then, for every vector $f$,
--
--   $$
--   Pf=P_0f+\sum_{k=1}^{\infty}\left[P_1(P_2P_1)^{k-1}+P_2(P_1P_2)^{k-1}-(P_2P_1)^k-(P_1P_2)^k\right]f.
--   $$
--
--   The series expresses projection onto the closed sum entirely through the two subspace projections and their intersection projection. In the paper it yields the corresponding reproducing-kernel expansion.
--
--   **Formalization Note** The displayed series means convergence of its finite partial sums in the norm of each vector, not convergence in operator norm. `ClosedSubmodule` join denotes the closure of the algebraic sum. No assumption that $F_1\cap F_2=\{0\}$ is made; that assumption begins later in §12.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 377, §12, Eq. (7)

import Mathlib
import Definitions.Def_AronszajnRK_SubspaceSum_sumProjection
import Definitions.Def_AronszajnRK_SubspaceSum_intersectionProjection

namespace AronszajnRK.SubspaceSum

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950),
§12, Eq. (7), p. 377 (PDF p. 41). Pointwise (strong), not operator-norm,
convergence of the projection series. The range index `k` is the paper's `k+1`. -/
theorem projection_sum_series {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (F₁ F₂ : ClosedSubmodule ℂ E) (f : E) :
    let P₁ : E →L[ℂ] E := (F₁ : Submodule ℂ E).starProjection
    let P₂ : E →L[ℂ] E := (F₂ : Submodule ℂ E).starProjection
    Filter.Tendsto
      (fun m : ℕ =>
        (intersectionProjection F₁ F₂ +
          ∑ k ∈ Finset.range m,
            (P₁ * (P₂ * P₁) ^ k + P₂ * (P₁ * P₂) ^ k -
              (P₂ * P₁) ^ (k + 1) - (P₁ * P₂) ^ (k + 1))) f)
      Filter.atTop (nhds (sumProjection F₁ F₂ f)) := by sorry

end AronszajnRK.SubspaceSum
