-- Prove2me | Theorems.Thm_CrowdContest_Pooling_lemma_2
-- name    : CrowdContest.Pooling.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:15.644771+00:00
-- url     : https://prove2.me/theorems/5c1e4a91-2672-4081-9b95-2bf80900d31c
-- title:
--   Lemma 2, p. 15 — C° is strictly increasing and strictly convex, and C°′(e°) = C¹′(ẽ¹) = C²′(ẽ²) at an interior optimal allocation
-- statement:
--   Let $C_1,C_2$ be cost functions (continuous on $[0,\infty)$, with positive first and second derivatives on $(0,\infty)$) and let
--   $$C^\circ(e)=\min\{C_1(e_1)+C_2(e_2) : e_1,e_2\ge 0,\ e_1+e_2=e\}$$
--   be the cost of aggregate effort $e$ under the optimal allocation over the two attributes. Then
--
--   1. $C^\circ$ is strictly increasing on $[0,\infty)$;
--   2. $C^\circ$ is strictly convex on $[0,\infty)$;
--   3. if $\tilde e_1,\tilde e_2>0$ is an optimal allocation of $e=\tilde e_1+\tilde e_2$, i.e. $C^\circ(e)=C_1(\tilde e_1)+C_2(\tilde e_2)$, then $C^\circ$ is differentiable at $e$ and
--   $$C^{\circ\prime}(e)=C_1'(\tilde e_1)=C_2'(\tilde e_2).$$
--
--   The lemma reduces the two-dimensional effort choice of the joint contest to a one-dimensional choice of aggregate effort with cost $C^\circ$.
--
--   **Formalization Note** The minimum is over nonnegative efforts, as efforts are nonnegative in the model. The first-order identity is asserted at an interior optimal allocation; at a boundary optimum it can fail, and the page's Lagrangian proof assumes an interior solution.
-- source:
--   Hu & Wang, Joint vs. Separate Crowdsourcing Contests, authors' accepted manuscript (TSpace; SSRN 2892683; Manag. Sci. doi:10.1287/mnsc.2020.3683), Lemma 2, p. 15; proof OA p. 1

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density
import Definitions.Def_CrowdContest_Pooling_Setting

open MeasureTheory

namespace CrowdContest.Pooling

/-- Lemma 2, p. 15: the cost of aggregate effort under the optimal allocation,
`C°(e) = min_{e₁ + e₂ = e} {C₁(e₁) + C₂(e₂)}`, is strictly increasing and strictly convex on
`[0, ∞)`; and at an interior optimal allocation `(ẽ₁, ẽ₂)` of `e = ẽ₁ + ẽ₂`,
`C°'(e) = C₁'(ẽ₁) = C₂'(ẽ₂)`. -/
theorem lemma_2 (C₁ C₂ : ℝ → ℝ) (hC₁ : IsCost C₁) (hC₂ : IsCost C₂) :
    StrictMonoOn (aggCost C₁ C₂) (Set.Ici 0) ∧
      StrictConvexOn ℝ (Set.Ici 0) (aggCost C₁ C₂) ∧
      ∀ e₁ e₂, 0 < e₁ → 0 < e₂ → aggCost C₁ C₂ (e₁ + e₂) = C₁ e₁ + C₂ e₂ →
        HasDerivAt (aggCost C₁ C₂) (deriv C₁ e₁) (e₁ + e₂) ∧ deriv C₁ e₁ = deriv C₂ e₂ := by sorry

end CrowdContest.Pooling
