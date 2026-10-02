-- Prove2me | Theorems.Thm_CarrollGR_riemann_symmetries
-- name    : CarrollGR.riemann_symmetries
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T00:02:55.938076+00:00
-- url     : https://prove2.me/theorems/93e9ad0d-f61c-479d-b8ea-0d6978d654ed
-- title:
--   Algebraic symmetries of the Riemann tensor
-- statement:
--   Let $g_{\mu\nu}$ be a spacetime metric on an open set $U$, and let $R_{\mu\nu\rho\sigma}=g_{\mu\lambda}R^\lambda{}_{\nu\rho\sigma}$ be its Riemann tensor (44) with all indices lowered. Then at every point of $U$ and for all indices
--
--   $$R_{\mu\nu\rho\sigma}=-R_{\mu\nu\sigma\rho}=-R_{\nu\mu\rho\sigma},\qquad R_{\mu\nu\rho\sigma}=R_{\rho\sigma\mu\nu},$$
--   $$R_{\mu\nu\rho\sigma}+R_{\mu\rho\sigma\nu}+R_{\mu\sigma\nu\rho}=0 .$$
--
--   These identities cut the $4^4=256$ components of the Riemann tensor down to 20 independent ones and imply that the Ricci tensor is symmetric.
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, p. 12, eq. (47)

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

theorem riemann_symmetries (g : TensorField2) (U : Set Coord) (hg : IsSpacetimeMetricOn g U)
    (x : Coord) (hx : x ∈ U) (μ ν ρ σ : Fin 4) :
    riemannLower g x μ ν ρ σ = -riemannLower g x μ ν σ ρ ∧
    riemannLower g x μ ν ρ σ = -riemannLower g x ν μ ρ σ ∧
    riemannLower g x μ ν ρ σ = riemannLower g x ρ σ μ ν ∧
    riemannLower g x μ ν ρ σ + riemannLower g x μ ρ σ ν + riemannLower g x μ σ ν ρ = 0 := by sorry

end CarrollGR
