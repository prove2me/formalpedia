-- Prove2me | Theorems.Thm_DiscreteConvex_EconomicEquilibrium_aggregate_cost_m_natural_convex
-- name    : DiscreteConvex.EconomicEquilibrium.aggregate_cost_m_natural_convex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T05:08:14.631204+00:00
-- url     : https://prove2.me/theorems/a22441f1-d58a-4ff4-b7a2-47c3bd96b6cf
-- title:
--   Proposition 11.12 -- the aggregate cost function is M$^\natural$-convex
-- statement:
--   **Proposition 11.12** (p.337). Let $U_h$ ($h \in H$) be M$^\natural$-concave functions with $\operatorname{dom} U_h$ bounded, and $C_l$ ($l \in L$) be M$^\natural$-convex functions with $\operatorname{dom} C_l$ bounded. Then the aggregate cost function $\Psi$ is M$^\natural$-convex, and $\partial_{\mathbb R}\Psi(x^\circ) \ne \emptyset$ for every $x^\circ \in \operatorname{dom}\Psi$.
--
--   This is the structural fact immediately underlying the existence proof: $\Psi$ (the integer infimal convolution of the cost functions and the negated utilities, Eq. (11.24)) inherits M$^\natural$-convexity from its M$^\natural$-convex/concave ingredients (chunk 06's Theorem 6.15), and a nonempty subdifferential is exactly what Proposition 11.10 needs to produce an equilibrium price.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337, Proposition 11.12.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337, Proposition 11.12

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_MNaturalConvex
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_UDom
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_BoundedSet
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_AggregateCost
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_SubdiffR

namespace DiscreteConvex.EconomicEquilibrium

open DiscreteConvex.MConvexFunctions

/-- Proposition 11.12 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.337). Let `Uh` (`h ∈ H`)
be M♮-concave functions with `dom Uh` bounded, and `Cl` (`l ∈ L`) be M♮-convex functions with
`dom Cl` bounded. Then the aggregate cost function `Ψ` is M♮-convex, and `∂R Ψ(x°) ≠ ∅` for every
`x° ∈ dom Ψ`. -/
theorem aggregate_cost_m_natural_convex {H K L : Type*} [Fintype H] [Fintype K] [Fintype L]
    [DecidableEq K] (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ)
    (hU : ∀ h, MNaturalConcave (U h)) (hUb : ∀ h, BoundedSet (UDom (U h)))
    (hC : ∀ l, MNaturalConvex (C l)) (hCb : ∀ l, BoundedSet (DomZ (C l))) :
    MNaturalConvex (AggregateCost U C) ∧
      ∀ x0 ∈ DomZ (AggregateCost U C), (SubdiffR (AggregateCost U C) x0).Nonempty := by sorry

end DiscreteConvex.EconomicEquilibrium
