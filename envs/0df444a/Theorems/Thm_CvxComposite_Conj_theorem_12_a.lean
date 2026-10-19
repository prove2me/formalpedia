-- Prove2me | Theorems.Thm_CvxComposite_Conj_theorem_12_a
-- name    : CvxComposite.Conj.theorem_12_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:42.069341+00:00
-- url     : https://prove2.me/theorems/829b5032-283f-4b62-afbc-88d937b874d3
-- title:
--   Theorem 12(a), p. 10 — conjugate bound by the closure of η
-- statement:
--   Let $K\subseteq E_2$ be a closed convex cone, $F:E_1\to E_2^\bullet$ a proper $K$-convex map, and $g\in\Gamma(E_2)$ satisfying condition (7): $g(F(x))\le g(y)$ whenever $x\in\operatorname{dom}F$ and $y-F(x)\in K$. Set
--   $$
--   \eta(p)=\inf_{v\in-K^\circ}\bigl(g^*(v)+\langle v,F\rangle^*(p)\bigr).
--   $$
--   Then $(g\circ F)^*(p)\le(\operatorname{cl}\eta)(p)$ for every $p$. Equality holds if every scalarization $\langle v,F\rangle$ with $v\in-K^\circ$ belongs to $\Gamma_0(E_1)$, $g$ is lower semicontinuous and $K$-increasing, and $\operatorname{rge}F\cap\operatorname{dom}g\ne\varnothing$.
--
--   The inequality is the first stage of the conjugacy formula; the equality clause gives the closed case.
--
--   **Formalization Note** The standing assumption $\operatorname{dom}F\ne\varnothing$ is explicit. The paper prints $\Gamma_0(E_2)$ for the scalarizations in this clause; their domain is $E_1$, and Lemma 10 uses $\Gamma_0(E_1)$, which is the reading formalized here.
-- source:
--   Burke, Hoheisel & Nguyen, A Study of Convex Convex-Composite Functions via Infimal Convolution with Applications, arXiv:1907.08318v2, p. 10, Theorem 12(a)

import Mathlib
import Definitions.Def_CvxComposite_Conj_Setting
open scoped InnerProductSpace Pointwise

namespace CvxComposite.Conj

open MoreauProx.Characterization MoreauProx.Decomposition

/-- Theorem 12(a), p. 10; Γ₀(E₂) in the printed equality hypothesis is read as Γ₀(E₁). -/
theorem theorem_12_a {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (K : Set E₂) (hK : IsClosedConvexCone K)
    (D : Set E₁) (hD : D.Nonempty) (F : E₁ → E₂) (hF : IsKConvex K D F)
    (g : E₂ → EReal) (hg : IsProperConvex g) (h7 : Cond7 K D F g) :
    (∀ p : E₁, conj (comp g D F) p ≤ lscHull (eta K D F g) p) ∧
    ((∀ v : E₂, -v ∈ polarCone K → GammaZero (scal v D F)) →
      LowerSemicontinuous g → KIncreasing K g →
      (F '' D ∩ effDom g).Nonempty →
      ∀ p : E₁, conj (comp g D F) p = lscHull (eta K D F g) p) := by sorry

end CvxComposite.Conj
