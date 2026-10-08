-- Prove2me | Theorems.Thm_ConvexOptAlg_StrongGD_lemma_3_11
-- name    : ConvexOptAlg.StrongGD.lemma_3_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:21:37.145846+00:00
-- url     : https://prove2.me/theorems/7af16fcd-79c0-4912-be49-c37c37e6259d
-- title:
--   Lemma 3.11, pp. 278–279 — improved co-coercivity for strongly convex smooth functions
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be $\alpha$-strongly convex and $\beta$-smooth with gradient $g$, where $n\ge1$ and $\alpha>0$. Then for all $x,y\in\mathbb R^n$,
--   $$\langle g(x)-g(y),x-y\rangle\ge\frac{\alpha\beta}{\alpha+\beta}\|x-y\|^2+\frac1{\alpha+\beta}\|g(x)-g(y)\|^2.$$
--
--   The inequality combines curvature and gradient regularity in the contraction analysis.
--
--   **Formalization Note** The statement includes the boundary case $\alpha=\beta$; no reciprocal of $\beta-\alpha$ appears.
-- source:
--   Bubeck, arXiv:1405.4980v2, Lemma 3.11, pp. 278–279

import Mathlib
import Definitions.Def_ConvexOptAlg_StrongGD_Defs
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn

open scoped InnerProductSpace

namespace ConvexOptAlg.StrongGD

/-- Lemma 3.11, pp. 278–279, including the case α = β. -/
theorem lemma_3_11 {n : ℕ} (hn : 0 < n) (f : E n → ℝ)
    (g : E n → E n) (α β : ℝ) (hα : 0 < α)
    (hsm : IsBetaSmooth f g β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α) :
    ∀ x y : E n,
      α * β / (β + α) * ‖x - y‖ ^ 2 +
          (1 / (β + α)) * ‖g x - g y‖ ^ 2 ≤
        ⟪g x - g y, x - y⟫_ℝ := by sorry

end ConvexOptAlg.StrongGD
