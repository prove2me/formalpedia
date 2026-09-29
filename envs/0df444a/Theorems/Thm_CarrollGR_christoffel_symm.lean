-- Prove2me | Theorems.Thm_CarrollGR_christoffel_symm
-- name    : CarrollGR.christoffel_symm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T23:54:42.290823+00:00
-- url     : https://prove2.me/theorems/82d55b7e-4697-440b-afb1-c684a7a95954
-- title:
--   Christoffel symbols are symmetric in their lower indices
-- statement:
--   Let $g_{\mu\nu}$ be a spacetime metric on an open set $U$ of a coordinate chart: smooth components and signature $(-+++)$ at every point of $U$. Then at every point $x\in U$ the Christoffel symbols
--   $\Gamma^\sigma_{\mu\nu}=\tfrac12 g^{\sigma\rho}(\partial_\mu g_{\nu\rho}+\partial_\nu g_{\rho\mu}-\partial_\rho g_{\mu\nu})$ satisfy
--
--   $$\Gamma^\sigma_{\mu\nu}(x)=\Gamma^\sigma_{\nu\mu}(x)\qquad\text{for all }\sigma,\mu,\nu .$$
--
--   Symmetry of the connection coefficients is what makes the Riemann tensor built from them have the symmetries (47).
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, p. 10, sentence after eq. (36)

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

theorem christoffel_symm (g : TensorField2) (U : Set Coord) (hg : IsSpacetimeMetricOn g U)
    (x : Coord) (hx : x ∈ U) (σ μ ν : Fin 4) :
    christoffel g σ μ ν x = christoffel g σ ν μ x := by sorry

end CarrollGR
