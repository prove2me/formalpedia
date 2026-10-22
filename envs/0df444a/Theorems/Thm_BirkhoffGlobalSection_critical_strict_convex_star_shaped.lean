-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_critical_strict_convex_star_shaped
-- name    : BirkhoffGlobalSection.critical_strict_convex_star_shaped
-- status  : Disproved
-- author  : @caleb
-- created : 2026-09-29T22:56:53.550971+00:00
-- url     : https://prove2.me/theorems/959b3da9-379b-44d0-94dd-96019aa4fc43
-- title:
--   Strict convexity at the critical parameters
-- statement:
--   At the critical parameters $\mu=1/2$, $c=2$, the elliptic-hyperbolic regularization gives a model whose image is strictly convex and star-shaped at every point outside any fixed open neighborhood $U$ of the saddle-center lifts $(\pm\tfrac12,0,0,0)$. Outside $U$ the critical surface stays a positive distance from the saddle-centers, where strict convexity holds.
--
--   This is the base computation: no parameter perturbation is involved, only the explicit reference model.
-- source:
--   Strict convexity of the equal-mass critical surface in elliptic-hyperbolic regularization (Liu--Salomao, Theorem 1.12, Section 9) and its persistence under small changes of parameters, as used in Section 10: https://arxiv.org/html/2506.17867v2.

import Definitions.Def_BirkhoffGlobalSection_RegularizationModel

namespace BirkhoffGlobalSection

theorem critical_strict_convex_star_shaped
    (U : Set Phase) (hU : IsOpen U)
    (hplus : (![1 / 2, 0, 0, 0] : Phase) ∈ U)
    (hminus : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U) :
    ∃ M₀ : RegularizationModel (1 / 2) 2,
      ∀ s ∈ leftEnergyComponent (1 / 2) 2, s ∉ U →
        IsStrictlyConvexStarShapedAt M₀.modelHamiltonian (M₀.toModel s) := by sorry

end BirkhoffGlobalSection
