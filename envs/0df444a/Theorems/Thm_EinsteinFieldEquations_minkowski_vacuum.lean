-- Prove2me | Theorems.Thm_EinsteinFieldEquations_minkowski_vacuum
-- name    : EinsteinFieldEquations.minkowski_vacuum
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T23:43:49.45455+00:00
-- url     : https://prove2.me/theorems/4f9f170f-53cc-4cb9-9fec-652fa26d5030
-- title:
--   Minkowski space is a vacuum solution
-- statement:
--   Flat Minkowski spacetime is a solution of the Einstein field equations with vanishing cosmological constant and vanishing stress–energy tensor.
--
--   Let $\eta = \operatorname{diag}(-1,1,1,1)$ be the Minkowski metric in inertial coordinates. Then for every value of the Einstein gravitational constant $\kappa$ and at every point $x$ of the chart,
--
--   $$G_{ab}(\eta)(x) + 0 \cdot \eta_{ab} \;=\; \kappa \cdot 0 \qquad (a, b \in \{0,1,2,3\}),$$
--
--   i.e. the Einstein tensor of $\eta$ vanishes identically. This is the statement, from the "Vacuum field equations" section of the source, that flat Minkowski space is the simplest vacuum solution.
-- source:
--   Wikipedia, "Einstein field equations", https://en.wikipedia.org/wiki/Einstein_field_equations, section "Vacuum field equations" ("Flat Minkowski space is the simplest example of a vacuum solution")

import Definitions.Def_efe_metrics

namespace EinsteinFieldEquations

theorem minkowski_vacuum (kappa : ℝ) (x : Coord) :
    SatisfiesEFE minkowski 0 kappa (fun _ => 0) x := by sorry

end EinsteinFieldEquations
