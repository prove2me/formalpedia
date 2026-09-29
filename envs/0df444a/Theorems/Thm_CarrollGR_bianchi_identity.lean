-- Prove2me | Theorems.Thm_CarrollGR_bianchi_identity
-- name    : CarrollGR.bianchi_identity
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:12:34.962073+00:00
-- url     : https://prove2.me/theorems/6a74678a-7ba5-4226-ac52-7c50aaaeb2e1
-- title:
--   Bianchi identity $\nabla_{[\lambda}R_{\mu\nu]\rho\sigma}=0$
-- statement:
--   Let $g_{\mu\nu}$ be a spacetime metric on an open set $U$ and $R_{\mu\nu\rho\sigma}$ its Riemann tensor with lowered indices. Then at every point of $U$ the covariant derivative (35) of the Riemann tensor satisfies
--
--   $$\nabla_{[\lambda}R_{\mu\nu]\rho\sigma}=0,$$
--
--   where the square brackets denote antisymmetrization (eqs. (16)–(17)):
--   $$\tfrac16\big(\nabla_\lambda R_{\mu\nu\rho\sigma}-\nabla_\lambda R_{\nu\mu\rho\sigma}+\nabla_\nu R_{\lambda\mu\rho\sigma}-\nabla_\mu R_{\lambda\nu\rho\sigma}+\nabla_\mu R_{\nu\lambda\rho\sigma}-\nabla_\nu R_{\mu\lambda\rho\sigma}\big)=0 .$$
--
--   This differential identity is the source of the contracted Bianchi identity (51) and hence of the compatibility of Einstein's equation with energy-momentum conservation.
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, p. 12, eq. (49) (antisymmetrization as in eqs. (16)–(17), p. 7)

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

theorem bianchi_identity (g : TensorField2) (U : Set Coord) (hg : IsSpacetimeMetricOn g U)
    (x : Coord) (hx : x ∈ U) (l μ ν ρ σ : Fin 4) :
    (1 / 6 : ℝ) * (covDerivLower4 g (riemannLower g) l μ ν ρ σ x
      - covDerivLower4 g (riemannLower g) l ν μ ρ σ x
      + covDerivLower4 g (riemannLower g) ν l μ ρ σ x
      - covDerivLower4 g (riemannLower g) μ l ν ρ σ x
      + covDerivLower4 g (riemannLower g) μ ν l ρ σ x
      - covDerivLower4 g (riemannLower g) ν μ l ρ σ x) = 0 := by sorry

end CarrollGR
