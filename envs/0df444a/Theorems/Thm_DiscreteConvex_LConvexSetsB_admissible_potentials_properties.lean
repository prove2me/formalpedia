-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexSetsB_admissible_potentials_properties
-- name    : DiscreteConvex.LConvexSetsB.admissible_potentials_properties
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:47:49.561381+00:00
-- url     : https://prove2.me/theorems/a9285f4f-1d74-4e27-8141-d22239f798b1
-- title:
--   Proposition 5.1 -- admissible_potentials_properties
-- statement:
--   **Proposition 5.1** (p.122). Let $\gamma$ be a distance function. (1) $D(\gamma) \ne \emptyset \iff$ no negative cycle exists in the graph $G_\gamma$. (2) If $D(\gamma) \ne \emptyset$, $\bar\gamma(u,v) = \sup\{p(v)-p(u) : p \in D(\gamma)\}$ and $D(\bar\gamma)=D(\gamma)$. (3) For $\gamma \in T[\mathbb R]$, $D(\gamma)$ is nonempty and $\gamma(u,v) = \sup\{p(v)-p(u) : p \in D(\gamma)\}$. (4) $D(\gamma)$ is an integral polyhedron for an integer-valued $\gamma$.
--
--   These are the fundamental facts, well known in network flow theory, connecting a distance function to its set of admissible potentials.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Proposition 5.1, Eq. (5.5)-(5.6).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Proposition 5.1

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSetsB_DistanceFunction
import Definitions.Def_DiscreteConvex_LConvexSetsB_AdmissiblePotentials
import Definitions.Def_DiscreteConvex_LConvexSetsB_NoNegativeCycle
import Definitions.Def_DiscreteConvex_LConvexSetsB_ShortestDist
import Definitions.Def_DiscreteConvex_LConvexSetsB_TriangleInequality
import Definitions.Def_DiscreteConvex_LConvexSetsB_IsIntegerValuedGamma
import Definitions.Def_DiscreteConvex_LConvexSetsB_IsIntegralPolyhedron

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.122, Proposition 5.1, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- Proposition 5.1 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.122). See the item's
`natural_language_statement` for the full statement. -/
theorem admissible_potentials_properties {V : Type*} [Fintype V] [DecidableEq V]
    (γ : V → V → WithTop ℝ) (hγ : DistanceFunction γ) :
    ((AdmissiblePotentials γ).Nonempty ↔ NoNegativeCycle γ) ∧
    ((AdmissiblePotentials γ).Nonempty →
      (∀ u v, ShortestDist γ u v = ⨆ p ∈ AdmissiblePotentials γ, (((p v - p u : ℝ)) : WithTop ℝ)) ∧
      AdmissiblePotentials (ShortestDist γ) = AdmissiblePotentials γ) ∧
    (TriangleInequality γ →
      (AdmissiblePotentials γ).Nonempty ∧
      (∀ u v, γ u v = ⨆ p ∈ AdmissiblePotentials γ, (((p v - p u : ℝ)) : WithTop ℝ))) ∧
    (IsIntegerValuedGamma γ → IsIntegralPolyhedron (AdmissiblePotentials γ)) := by sorry

end DiscreteConvex.LConvexSetsB
