-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSetsB_base_polyhedron_nonempty
-- name    : DiscreteConvex.MConvexSetsB.base_polyhedron_nonempty
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:28:56.989996+00:00
-- url     : https://prove2.me/theorems/68ff8989-58d9-46ef-96f4-613a6273f95d
-- title:
--   Proposition 4.4 -- base_polyhedron_nonempty
-- statement:
--   **Proposition 4.4** (p.105). $B(\rho)$ is nonempty for $\rho \in S[\mathbb R]$: every submodular set function with $\rho(\emptyset)=0$ and $\rho(V)<+\infty$ has at least one base.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.105, Proposition 4.4.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.105, Proposition 4.4

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.105, Proposition 4.4, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Proposition 4.4 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.105). See the item's
`natural_language_statement` for the full statement. -/
theorem base_polyhedron_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) :
    (BasePolyhedron ρ).Nonempty := by sorry

end DiscreteConvex.MConvexSetsB
