-- Prove2me | Theorems.Thm_AronszajnRK_SubspaceSum_projection_identity
-- name    : AronszajnRK.SubspaceSum.projection_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:12:32.037493+00:00
-- url     : https://prove2.me/theorems/43c38e6a-ce53-4522-9d0b-135d8da60886
-- title:
--   §12, Eq. (1) — finite projection identity
-- statement:
--   Let $F_1,F_2$ be closed subspaces of a complex Hilbert space. Write $P_i$ for projection onto $F_i$ and $P$ for projection onto $\overline{F_1+F_2}$. For every integer $m\ge1$,
--
--   $$
--   [(P-P_1)(P-P_2)]^m=P-\sum_{k=1}^{m}\left[P_1(P_2P_1)^{k-1}+P_2(P_1P_2)^{k-1}-(P_2P_1)^k-(P_1P_2)^k\right]-(P_2P_1)^m.
--   $$
--
--   This finite identity isolates the two powers whose strong limits determine the series for $P$.
--
--   **Formalization Note** Operator multiplication means composition, with the right factor applied first. The finite sum uses Lean indices $0,\dots,m-1$, representing the paper's $1,\dots,m$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 375, §12, Eq. (1)

import Mathlib
import Definitions.Def_AronszajnRK_SubspaceSum_sumProjection

namespace AronszajnRK.SubspaceSum

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950),
§12, Eq. (1), p. 375 (PDF p. 39). The finite projection identity for m ≥ 1.
The `Finset.range m` index `k` represents the paper's index `k+1`. -/
theorem projection_identity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (F₁ F₂ : ClosedSubmodule ℂ E) (m : ℕ) (hm : 1 ≤ m) :
    let P : E →L[ℂ] E := sumProjection F₁ F₂
    let P₁ : E →L[ℂ] E := (F₁ : Submodule ℂ E).starProjection
    let P₂ : E →L[ℂ] E := (F₂ : Submodule ℂ E).starProjection
    ((P - P₁) * (P - P₂)) ^ m =
      P - (∑ k ∈ Finset.range m,
        (P₁ * (P₂ * P₁) ^ k + P₂ * (P₁ * P₂) ^ k -
          (P₂ * P₁) ^ (k + 1) - (P₁ * P₂) ^ (k + 1))) -
        (P₂ * P₁) ^ m := by sorry

end AronszajnRK.SubspaceSum
