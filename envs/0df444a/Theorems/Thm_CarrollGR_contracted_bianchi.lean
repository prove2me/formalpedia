-- Prove2me | Theorems.Thm_CarrollGR_contracted_bianchi
-- name    : CarrollGR.contracted_bianchi
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:12:56.887986+00:00
-- url     : https://prove2.me/theorems/52eaf064-c713-4cab-8e86-059b79527302
-- title:
--   Contracted Bianchi identity $\nabla_\mu G^{\mu\nu}=0$
-- statement:
--   Let $g_{\mu\nu}$ be a spacetime metric on an open set $U$, and let $G^{\mu\nu}=g^{\mu\alpha}g^{\nu\beta}G_{\alpha\beta}$ be its Einstein tensor $G_{\mu\nu}=R_{\mu\nu}-\tfrac12Rg_{\mu\nu}$ with both indices raised. Then at every point of $U$ and for every $\nu$
--
--   $$\nabla_\mu G^{\mu\nu}=0 .$$
--
--   Combined with Einstein's equation, this identity guarantees the local conservation law $\nabla_\mu T^{\mu\nu}=0$ (eq. (60)).
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, p. 13, eq. (51)

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

theorem contracted_bianchi (g : TensorField2) (U : Set Coord) (hg : IsSpacetimeMetricOn g U)
    (x : Coord) (hx : x ∈ U) (ν : Fin 4) :
    ∑ μ : Fin 4, covDerivUpper2 g (einsteinUpper g) μ μ ν x = 0 := by sorry

end CarrollGR
