-- Prove2me | Theorems.Thm_CvxComposite_Conj_theorem_2
-- name    : CvxComposite.Conj.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:41.474485+00:00
-- url     : https://prove2.me/theorems/f9ef189b-4d88-4395-a5af-7002b02a9dbf
-- title:
--   Theorem 2, p. 5 — conjugacy and infimal convolution (closure identity under dom cl f ∩ dom cl g ≠ ∅)
-- statement:
--   Let $f,g\in\Gamma(E)$ on a finite-dimensional Euclidean space $E$, and let $\operatorname{cl}$ denote the lower semicontinuous hull. If $\operatorname{dom}(\operatorname{cl}f)\cap\operatorname{dom}(\operatorname{cl}g)\ne\varnothing$, their conjugates and lower semicontinuous hulls satisfy
--   $$
--   (\operatorname{cl}f+\operatorname{cl}g)^*
--     =\operatorname{cl}(f^*\mathbin{\square}g^*).
--   $$
--   If $\operatorname{ri}(\operatorname{dom}f)\cap\operatorname{ri}(\operatorname{dom}g)\ne\varnothing$, the closure operations can be removed, and for every $y$ the infimum is attained:
--   $$
--   (f+g)^*(y)=\min_{u\in E}\bigl\{f^*(u)+g^*(y-u)\bigr\}.
--   $$
--
--   This sum rule is the conjugacy result used in the derivation of the paper's composite formula.
--
--   **Formalization Note** Relative interior is the intrinsic interior of a set. Attainment is asserted for every $y$; outside the effective domain of the infimal convolution the minimum value is $+\infty$. The closure identity carries the hypothesis $\operatorname{dom}(\operatorname{cl}f)\cap\operatorname{dom}(\operatorname{cl}g)\ne\varnothing$, which the page does not print: the paper defines $\operatorname{cl}$ as the lower semicontinuous hull (p. 4), and with that reading the unconditional identity is false when $\operatorname{cl}f+\operatorname{cl}g\equiv+\infty$. For example, on $\mathbb{R}^2$ take $f=\delta_{\{x_2\ge e^{x_1}\}}$ and $g=\delta_{\{x_2\le 0\}}$: the left side is $-\infty$ everywhere, while $f^*\mathbin{\square}g^*$ is $+\infty$ on the open half-plane $\{x_1<0\}$, so its lower semicontinuous hull is $+\infty$ there. The cited source, Rockafellar's Theorem 16.4, uses a closure that is identically $-\infty$ for improper functions. The added hypothesis is exactly the case in which $f^*\mathbin{\square}g^*$ is proper and the two closures agree. The qualified part already implies it.
-- source:
--   Burke, Hoheisel & Nguyen, A Study of Convex Convex-Composite Functions via Infimal Convolution with Applications, arXiv:1907.08318v2, p. 5, Theorem 2 (citing Rockafellar, Convex Analysis, Theorem 16.4)

import Mathlib
import Definitions.Def_CvxComposite_Conj_Setting
open scoped InnerProductSpace Pointwise

namespace CvxComposite.Conj

open MoreauProx.Characterization

/-- Theorem 2, p. 5: conjugacy of a sum and infimal convolution.
The closure identity carries the hypothesis `dom (cl f) ∩ dom (cl g) ≠ ∅`: with the paper's
`cl` = lower semicontinuous hull (p. 4) the printed identity fails when `cl f + cl g ≡ +∞`
(e.g. `f`, `g` the indicators of `{x₂ ≥ exp x₁}` and `{x₂ ≤ 0}` in `ℝ²`: the left side is `−∞` everywhere, the
right side is `+∞` on `{x₁ < 0}`); the cited [47, Thm 16.4] uses Rockafellar's closure, which
is the constant `−∞` for an improper function. -/
theorem theorem_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f g : E → EReal)
    (hf : IsProperConvex f) (hg : IsProperConvex g) :
    ((effDom (lscHull f) ∩ effDom (lscHull g)).Nonempty →
      conj (fun x => lscHull f x + lscHull g x) =
        lscHull (infConv (conj f) (conj g))) ∧
    ((intrinsicInterior ℝ (effDom f) ∩ intrinsicInterior ℝ (effDom g)).Nonempty →
      ∀ y : E, conj (fun x => f x + g x) y = infConv (conj f) (conj g) y ∧
        ∃ u : E, infConv (conj f) (conj g) y = conj f u + conj g (y - u)) := by sorry

end CvxComposite.Conj
