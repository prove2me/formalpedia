-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSetsB_mconvex_induces_submodular
-- name    : DiscreteConvex.MConvexSetsB.mconvex_induces_submodular
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:31:08.07463+00:00
-- url     : https://prove2.me/theorems/0a7baa37-b2e4-49d2-ac44-06c98e215bf3
-- title:
--   Proposition 4.13 -- mconvex_induces_submodular
-- statement:
--   **Proposition 4.13** (p.108-109), Eq. (4.25). For an M-convex set $B$, define $\rho(X) = \sup\{x(X) : x \in B\}$. Then (1) $\rho \in S[\mathbb Z]$, and (2) $\overline B = B(\rho)$: the convex hull of $B$ is exactly the base polyhedron of the induced submodular function $\rho$.
--
--   **Formalization Note.** As in Theorem 4.12, the book's "$B=B(\rho)$" in part (2) denotes the convex hull $\overline B$ (the surrounding text calls $B(\rho)$ the polyhedral description of the M-convex polyhedron, i.e. the convex hull of $B$), formalized as `convexHull ℝ (IntEmbed B)`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.108-109, Proposition 4.13, Eq. (4.25).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.108-109, Proposition 4.13

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSetsB_InducedRho
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntEmbed
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.108-109, Proposition 4.13, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Proposition 4.13 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.108-109). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_induces_submodular {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ))
    (hExc : ExchangeAxiomB B) (hBne : B.Nonempty) :
    SubmodularSetFunction (InducedRho B) ∧ IsIntegerValued (InducedRho B) ∧
      convexHull ℝ (IntEmbed B) = BasePolyhedron (InducedRho B) := by sorry

end DiscreteConvex.MConvexSetsB
