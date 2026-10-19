-- Prove2me | Theorems.Thm_CvxComposite_Conj_theorem_12_b
-- name    : CvxComposite.Conj.theorem_12_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:58.687728+00:00
-- url     : https://prove2.me/theorems/a243f851-9b21-4477-afed-89b8ba27e1e1
-- title:
--   Theorem 12(b), p. 10 — η is closed proper convex and attains its infimum
-- statement:
--   Under the assumptions of Theorem 12(a), assume the Slater-type condition
--   $$
--   F\bigl(\operatorname{ri}(\operatorname{dom}F)\bigr)
--     \cap\operatorname{ri}(\operatorname{dom}g-K)\ne\varnothing.
--   $$
--   Then the function $\eta(p)=\inf_{v\in-K^\circ}\{g^*(v)+\langle v,F\rangle^*(p)\}$ is closed, proper, and convex. Moreover, for every $p\in E_1$ there is a $v\in-K^\circ$ such that
--   $$
--   \eta(p)=g^*(v)+\langle v,F\rangle^*(p).
--   $$
--
--   The theorem supplies a well-behaved dual function and attainment for the goal theorem.
--
--   **Formalization Note** The standing assumption $\operatorname{dom}F\ne\varnothing$ is explicit. The attainment claim includes points where $\eta(p)=+\infty$, in agreement with the paper's “possibly $+\infty$” qualification.
-- source:
--   Burke, Hoheisel & Nguyen, A Study of Convex Convex-Composite Functions via Infimal Convolution with Applications, arXiv:1907.08318v2, p. 10, Theorem 12(b), condition (10)

import Mathlib
import Definitions.Def_CvxComposite_Conj_Setting
open scoped InnerProductSpace Pointwise

namespace CvxComposite.Conj

open MoreauProx.Characterization MoreauProx.Decomposition

/-- Theorem 12(b), p. 10: the qualified dual value is in Γ₀ and its infimum is attained. -/
theorem theorem_12_b {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (K : Set E₂) (hK : IsClosedConvexCone K)
    (D : Set E₁) (hD : D.Nonempty) (F : E₁ → E₂) (hF : IsKConvex K D F)
    (g : E₂ → EReal) (hg : IsProperConvex g) (h7 : Cond7 K D F g)
    (h10 : (F '' intrinsicInterior ℝ D ∩ intrinsicInterior ℝ (effDom g - K)).Nonempty) :
    GammaZero (eta K D F g) ∧
      ∀ p : E₁, ∃ v : E₂, -v ∈ polarCone K ∧
        eta K D F g p = conj g v + conj (scal v D F) p := by sorry

end CvxComposite.Conj
