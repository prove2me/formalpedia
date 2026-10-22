-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_eh_critical_half_mass_strictly_convex_off_saddle
-- name    : BirkhoffGlobalSection.eh_critical_half_mass_strictly_convex_off_saddle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T20:09:05.543676+00:00
-- url     : https://prove2.me/theorems/595d26f4-ae74-43d9-8c8b-5fc68113ee55
-- title:
--   Strict convexity of the equal-mass critical EH surface off the saddle-centers
-- statement:
--   Strict convexity of the equal-mass critical surface away from its saddle-centers, in the centered elliptic-hyperbolic (EH) coordinates $(x_1,x_2,y_1,y_2)$ of Liu–Salomão, Section 9.2.
--
--   Let $G=G_{1/2,2}$ be the EH Hamiltonian at $\mu=\tfrac12$ and the critical energy $c=2$. Let $s$ be a zero of $G$ with
--   $$|x_2|\le \tfrac{\pi}{2},\qquad \cosh^2 x_1\le 4,$$
--   other than the two saddle-centers $\sigma_\pm=(0,\pm\tfrac{\pi}{2},0,0)$. Then $s$ is a strictly convex star-shaped point of $G$: the tangential Hessian is positive definite and $dG_s(s)>0$.
--
--   This is Theorem 1.12 of Liu–Salomão on the left lobe. For $c>2$ the same region carries the accepted theorems `eh_half_mass_tangential_hessian` and `eh_half_mass_star_shaped`. At $c=2$ the inequalities stay strict except at $\sigma_\pm$, where the gradient vanishes.
--
--   **Formalization Note** The region $|x_2|\le\pi/2$, $\cosh^2x_1\le 4$ selects the left lobe; the right lobe lies in $|x_2|\ge\pi/2$ and meets it only at $\sigma_\pm$. The conclusion is `IsStrictlyConvexStarShapedAt` from `Def_BirkhoffGlobalSection_RegularizationModel`.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2 (Theorem 1.12, Sections 9.2-9.3 and 10); reduction of regularization_model_convex_away_from_saddle_center.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical

namespace BirkhoffGlobalSection

/-- Strict convexity of the equal-mass critical surface away from its saddle-centers, in the
centered elliptic-hyperbolic coordinates: at `μ = 1/2`, `c = 2`, every zero of the EH
Hamiltonian with `|x₂| ≤ π/2` and `cosh² x₁ ≤ 4`, other than the two saddle-centers
`(0, ±π/2, 0, 0)`, is a strictly convex star-shaped point. -/
theorem eh_critical_half_mass_strictly_convex_off_saddle (s : Phase)
    (hs : ehLeftHamiltonian (1 / 2) 2 s = 0)
    (h1 : |s 1| ≤ Real.pi / 2) (h0 : Real.cosh (s 0) ^ 2 ≤ 4)
    (hplus : s ≠ ![0, Real.pi / 2, 0, 0]) (hminus : s ≠ ![0, -(Real.pi / 2), 0, 0]) :
    IsStrictlyConvexStarShapedAt (ehLeftHamiltonian (1 / 2) 2) s := by sorry

end BirkhoffGlobalSection
