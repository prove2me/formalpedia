-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSetsB_base_polyhedron_integral
-- name    : DiscreteConvex.MConvexSetsB.base_polyhedron_integral
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:29:02.84323+00:00
-- url     : https://prove2.me/theorems/e908b807-4e87-4362-8bc8-fa3fabf43508
-- title:
--   Proposition 4.6 -- base_polyhedron_integral
-- statement:
--   **Proposition 4.6** (p.107). $B(\rho)$ is an integral polyhedron for $\rho \in S[\mathbb Z]$: an integer-valued submodular function's base polyhedron is the convex hull of its own integer points.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.107, Proposition 4.6.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.107, Proposition 4.6

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegralPolyhedron

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.107, Proposition 4.6, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Proposition 4.6 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.107). See the item's
`natural_language_statement` for the full statement. -/
theorem base_polyhedron_integral {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (hInt : IsIntegerValued ρ) :
    IsIntegralPolyhedron (BasePolyhedron ρ) := by sorry

end DiscreteConvex.MConvexSetsB
