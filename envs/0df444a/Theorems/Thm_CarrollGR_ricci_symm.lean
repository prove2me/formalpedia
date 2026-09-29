-- Prove2me | Theorems.Thm_CarrollGR_ricci_symm
-- name    : CarrollGR.ricci_symm
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:04:25.98079+00:00
-- url     : https://prove2.me/theorems/65c665bf-4248-40ea-be34-942921243d2c
-- title:
--   The Ricci tensor is symmetric
-- statement:
--   Let $g_{\mu\nu}$ be a spacetime metric on an open set $U$. Then its Ricci tensor $R_{\alpha\beta}=R^\lambda{}_{\alpha\lambda\beta}$ is symmetric at every point of $U$:
--
--   $$R_{\mu\nu}=R_{\nu\mu}.$$
--
--   Symmetry of the Ricci tensor is needed for the Einstein equation to relate two symmetric tensors.
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, p. 12, eq. (48)

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

theorem ricci_symm (g : TensorField2) (U : Set Coord) (hg : IsSpacetimeMetricOn g U)
    (x : Coord) (hx : x ∈ U) (μ ν : Fin 4) :
    ricci g μ ν x = ricci g ν μ x := by sorry

end CarrollGR
