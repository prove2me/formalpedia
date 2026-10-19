-- Prove2me | Theorems.Thm_CvxComposite_Conj_theorem_12_c
-- name    : CvxComposite.Conj.theorem_12_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:50.334708+00:00
-- url     : https://prove2.me/theorems/3740b5b8-edd0-4304-815a-2f9b01f5540c
-- title:
--   Theorem 12(c), p. 10 — attained conjugate formula and domain
-- statement:
--   Let $K\subseteq E_2$ be a closed convex cone, $F:E_1\to E_2^\bullet$ a proper $K$-convex map, and $g\in\Gamma(E_2)$ satisfy condition (7). Assume the Slater-type condition $F(\operatorname{ri}(\operatorname{dom}F))\cap\operatorname{ri}(\operatorname{dom}g-K)\ne\varnothing$. Then, for every $p\in E_1$, the minimum is attained and
--   $$
--   (g\circ F)^*(p)=\min_{v\in-K^\circ}
--     \bigl\{g^*(v)+\langle v,F\rangle^*(p)\bigr\}.
--   $$
--   Its effective domain is exactly
--   $$
--   \operatorname{dom}(g\circ F)^*
--     =\{p\in E_1:\exists v\in\operatorname{dom}g^*\cap(-K^\circ),\
--         \langle v,F\rangle^*(p)<+\infty\}.
--   $$
--
--   This identifies both the value and the finite domain of the composite's Fenchel conjugate under a point-based qualification condition.
--
--   **Formalization Note** The standing properness of $F$ is explicit. The map is represented by its domain $D$ and a total representative whose off-domain values are ignored; $\operatorname{ri}$ is intrinsic interior. The minimum is encoded by equality to $\eta$ plus an attaining $v\in-K^\circ$.
-- source:
--   Burke, Hoheisel & Nguyen, A Study of Convex Convex-Composite Functions via Infimal Convolution with Applications, arXiv:1907.08318v2, p. 10, Theorem 12(c)

import Mathlib
import Definitions.Def_CvxComposite_Conj_Setting
open scoped InnerProductSpace Pointwise

namespace CvxComposite.Conj

open MoreauProx.Characterization MoreauProx.Decomposition

/-- Theorem 12(c), p. 10: the attained conjugacy formula and effective domain. -/
theorem theorem_12_c {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (K : Set E₂) (hK : IsClosedConvexCone K)
    (D : Set E₁) (hD : D.Nonempty) (F : E₁ → E₂) (hF : IsKConvex K D F)
    (g : E₂ → EReal) (hg : IsProperConvex g) (h7 : Cond7 K D F g)
    (h10 : (F '' intrinsicInterior ℝ D ∩ intrinsicInterior ℝ (effDom g - K)).Nonempty) :
    (∀ p : E₁, conj (comp g D F) p = eta K D F g p ∧
      ∃ v : E₂, -v ∈ polarCone K ∧
        conj (comp g D F) p = conj g v + conj (scal v D F) p) ∧
    effDom (conj (comp g D F)) =
      {p | ∃ v ∈ effDom (conj g), -v ∈ polarCone K ∧
        conj (scal v D F) p < ⊤} := by sorry

end CvxComposite.Conj
