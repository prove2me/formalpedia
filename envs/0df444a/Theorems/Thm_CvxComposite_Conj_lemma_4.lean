-- Prove2me | Theorems.Thm_CvxComposite_Conj_lemma_4
-- name    : CvxComposite.Conj.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:52.008624+00:00
-- url     : https://prove2.me/theorems/1cf8f00a-0212-4035-a6ce-36884ffbda5c
-- title:
--   Lemma 4, p. 6 — relative interior of a K-epigraph
-- statement:
--   Let $K\subseteq E_2$ be a convex cone and $F:E_1\to E_2^\bullet$ a proper $K$-convex map with domain $D$. Then
--   $$
--   \operatorname{ri}(K\text{-epi}F)
--     =\{(x,v):x\in\operatorname{ri}D,\ v-F(x)\in\operatorname{ri}K\}
--     =((\operatorname{ri}K)\text{-epi}F)\cap(\operatorname{ri}D\times E_2).
--   $$
--   If $D=E_1$, the last intersection can be omitted.
--
--   This identifies the relative interior needed to express the Slater-type condition in Theorem 12 through the images of the domains.
--
--   **Formalization Note** The cone need not be closed. Properness means $D\ne\varnothing$. Relative interior is `intrinsicInterior`; $F$ is represented by $(D,F)$.
-- source:
--   Burke, Hoheisel & Nguyen, A Study of Convex Convex-Composite Functions via Infimal Convolution with Applications, arXiv:1907.08318v2, p. 6, Lemma 4

import Mathlib
import Definitions.Def_CvxComposite_Conj_Setting
open scoped InnerProductSpace Pointwise

namespace CvxComposite.Conj

/-- Lemma 4, p. 6: relative interior of the K-epigraph of a proper K-convex map. -/
theorem lemma_4 {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (K : Set E₂) (hK : IsConvexConeSet K)
    (D : Set E₁) (hD : D.Nonempty) (F : E₁ → E₂) (hF : IsKConvex K D F) :
    intrinsicInterior ℝ (KEpi K D F) =
      {q | q.1 ∈ intrinsicInterior ℝ D ∧ q.2 - F q.1 ∈ intrinsicInterior ℝ K} ∧
    intrinsicInterior ℝ (KEpi K D F) =
      KEpi (intrinsicInterior ℝ K) D F ∩ (intrinsicInterior ℝ D ×ˢ Set.univ) ∧
    (D = Set.univ →
      intrinsicInterior ℝ (KEpi K D F) = KEpi (intrinsicInterior ℝ K) D F) := by sorry

end CvxComposite.Conj
