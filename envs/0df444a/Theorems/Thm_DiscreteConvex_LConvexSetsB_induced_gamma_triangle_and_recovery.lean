-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexSetsB_induced_gamma_triangle_and_recovery
-- name    : DiscreteConvex.LConvexSetsB.induced_gamma_triangle_and_recovery
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:45:38.513335+00:00
-- url     : https://prove2.me/theorems/827680eb-5e6b-4b4f-8a98-5a5e60d04f5b
-- title:
--   Proposition 5.3 -- induced_gamma_triangle_and_recovery
-- statement:
--   **Proposition 5.3** (p.124), Eq. (5.8). For nonempty $D \subseteq \mathbb Z^V$, define $\gamma(u,v) = \sup\{p(v)-p(u) : p \in D\}$. Then (1) $\gamma$ satisfies the triangle inequality, i.e. $\gamma \in T[\mathbb Z]$, and (2) if $D$ is an L-convex set, $\overline D = D(\gamma)$.
--
--   **Formalization Note.** As in Theorem 5.2 (chunk `05-lconvex-sets`), the book's "$D=D(\gamma)$" in part (2) denotes the convex hull $\overline D$ (the surrounding text introduces $D(\gamma)$ here as the polyhedral description of the convex hull of an L-convex set), formalized as `convexHull ℝ (IntEmbed D)`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.124, Proposition 5.3, Eq. (5.8).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.124, Proposition 5.3

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSetsB_TriangleInequality
import Definitions.Def_DiscreteConvex_LConvexSetsB_InducedGamma
import Definitions.Def_DiscreteConvex_LConvexSetsB_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexSetsB_IntEmbed
import Definitions.Def_DiscreteConvex_LConvexSetsB_AdmissiblePotentials

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.124, Proposition 5.3, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- Proposition 5.3 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.124). See the item's
`natural_language_statement` for the full statement. -/
theorem induced_gamma_triangle_and_recovery {V : Type*} [Fintype V] [DecidableEq V]
    (D : Set (V → ℤ)) (hDne : D.Nonempty) :
    TriangleInequality (InducedGamma D) ∧
    (LConvexSet D → convexHull ℝ (IntEmbed D) = AdmissiblePotentials (InducedGamma D)) := by sorry

end DiscreteConvex.LConvexSetsB
