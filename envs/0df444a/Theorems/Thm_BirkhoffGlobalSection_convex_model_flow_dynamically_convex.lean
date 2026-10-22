-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_flow_dynamically_convex
-- name    : BirkhoffGlobalSection.convex_model_flow_dynamically_convex
-- status  : Open
-- author  : @caleb
-- created : 2026-09-28T03:19:22.651522+00:00
-- url     : https://prove2.me/theorems/5f08e79b-87c2-4f82-8f2a-eb84c61aa622
-- title:
--   Dynamical convexity of a convex regularization model
-- statement:
--   Let $M$ be a convex regularization model with model Hamiltonian $H_M$ and convex body $B$. Then the model Hamiltonian flow on the boundary surface $\partial B$ is dynamically convex: every closed model orbit, including every multiple cover, has transverse winding above one, i.e. Conley--Zehnder index at least $3$.
--
--   $$
--   \mathrm{IsDynamicallyConvexOn}(H_M, \partial B).
--   $$
--
--   This is the Hofer--Wysocki--Zehnder theorem in the regularization coordinates: the positive tangential Hessian of $H_M$ on $\partial B$ forces the index bound. It supplies the dynamical-convexity input for the rational disk theorem, with no retrograde or binding hypothesis.
-- source:
--   Hryniewicz--Salomao, https://arxiv.org/html/1505.02713v3, Corollary 1.8 and Section 4; Liu--Salomao, https://arxiv.org/html/2506.17867v2, Theorem 1.16(ii) (transverse Hopf-fiber clause) and Section 10. Coordinate-level specialization to a centrally symmetric strictly convex model.

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel

namespace BirkhoffGlobalSection

theorem convex_model_flow_dynamically_convex {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) :
    IsDynamicallyConvexOn M.modelHamiltonian (frontier M.body) := by sorry

end BirkhoffGlobalSection
