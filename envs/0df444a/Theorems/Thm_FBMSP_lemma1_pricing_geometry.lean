-- Prove2me | Theorems.Thm_FBMSP_lemma1_pricing_geometry
-- name    : FBMSP.lemma1_pricing_geometry
-- status  : Open
-- author  : @mikeh
-- created : 2026-10-30T04:54:21.909304+00:00
-- url     : https://prove2.me/theorems/214efd13-fc8f-454b-b462-0b737d7688f5
-- title:
--   Lemma 1 — Margin monotonicity and revenue geometry
-- statement:
--   For general integrable mean-zero error, let $p_\epsilon(x)$ be the least optimal price, $\theta_\epsilon(x)=p_\epsilon(x)-x$, and $R_\epsilon(x)$ the optimal customer revenue. The margin is nonincreasing on positive predicted values. If $0<x_1<x_2$, then
--   $$S(\theta_\epsilon(x_1))(x_2-x_1)\le R_\epsilon(x_2)-R_\epsilon(x_1)\le S(\theta_\epsilon(x_2))(x_2-x_1).$$
--   Moreover, revenue is convex, continuous, nondecreasing, and 1-Lipschitz on that domain. No MHR assumption is imposed.
--
--   **Formalization note.** Weak monotonicity is intended. The 1-Lipschitz conclusion follows from the source bounds and $0\le S\le1$. The optional derivative formula at continuity points is outside this target.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Lemma 1(a)–(c), p.11; proof pp.38–39 (ec4–ec5).

import Definitions.Def_FBMSP_Model

namespace FBMSP

/-- Lemma 1(a)--(c), with the 1-Lipschitz consequence of its secant bounds.
The optional derivative-at-continuity-points refinement is not asserted in
this target.  Draft statement; proof remains open. -/
theorem lemma1_pricing_geometry (η : MeasureTheory.Measure ℝ)
    (hnoise : ValidNoise η) :
    AntitoneOn (margin η) (Set.Ioi (0 : ℝ)) ∧
    (∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ →
      survival η (margin η x₁) * (x₂ - x₁) ≤
          singleRevenue η x₂ - singleRevenue η x₁ ∧
        singleRevenue η x₂ - singleRevenue η x₁ ≤
          survival η (margin η x₂) * (x₂ - x₁)) ∧
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (singleRevenue η) ∧
    ContinuousOn (singleRevenue η) (Set.Ioi (0 : ℝ)) ∧
    MonotoneOn (singleRevenue η) (Set.Ioi (0 : ℝ)) ∧
    LipschitzOnWith 1 (singleRevenue η) (Set.Ioi (0 : ℝ)) := by sorry

end FBMSP
