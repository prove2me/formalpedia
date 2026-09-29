-- Prove2me | Theorems.Thm_CarrollGR_metric_compatibility
-- name    : CarrollGR.metric_compatibility
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T00:02:24.722081+00:00
-- url     : https://prove2.me/theorems/ff699ea8-72c8-456e-a75c-60c76d1816d2
-- title:
--   Metric compatibility: $\nabla_\sigma g_{\mu\nu}=0$ and $\nabla_\sigma g^{\mu\nu}=0$
-- statement:
--   Let $g_{\mu\nu}$ be a spacetime metric on an open set $U$ (smooth, signature $(-+++)$), with Christoffel symbols (36) and covariant derivative (35). Then at every point of $U$ and for all indices
--
--   $$\nabla_\sigma g_{\mu\nu}=\partial_\sigma g_{\mu\nu}-\Gamma^\lambda_{\sigma\mu}g_{\lambda\nu}-\Gamma^\lambda_{\sigma\nu}g_{\mu\lambda}=0,$$
--   $$\nabla_\sigma g^{\mu\nu}=\partial_\sigma g^{\mu\nu}+\Gamma^\mu_{\sigma\lambda}g^{\lambda\nu}+\Gamma^\nu_{\sigma\lambda}g^{\mu\lambda}=0 .$$
--
--   Metric compatibility is the defining property of the Christoffel connection and is what allows indices to be raised and lowered through covariant derivatives.
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, p. 10, eq. (37)

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

theorem metric_compatibility (g : TensorField2) (U : Set Coord) (hg : IsSpacetimeMetricOn g U)
    (x : Coord) (hx : x ∈ U) (σ μ ν : Fin 4) :
    covDerivLower2 g g σ μ ν x = 0 ∧ covDerivUpper2 g (invMetric g) σ μ ν x = 0 := by sorry

end CarrollGR
