-- Prove2me | Theorems.Thm_DiscreteConvex_EconomicEquilibrium_equilibrium_price_set_l_natural_convex
-- name    : DiscreteConvex.EconomicEquilibrium.equilibrium_price_set_l_natural_convex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T05:30:18.523047+00:00
-- url     : https://prove2.me/theorems/e4a6349f-a675-43ec-adff-8ae55249e57e
-- title:
--   Theorem 11.16 -- the equilibrium price set is an L$^\natural$-convex polyhedron
-- statement:
--   **Theorem 11.16** (p.339). Suppose that utility functions $U_h$ ($h \in H$) are M$^\natural$-concave and cost functions $C_l$ ($l \in L$) are M$^\natural$-convex, and that there exists an equilibrium for a total initial endowment $x^\circ$. Then the set $P^*(x^\circ)$ of all equilibrium price vectors is an L$^\natural$-convex polyhedron. This means, in particular, that $p, q \in P^*(x^\circ) \Rightarrow p \vee q, p \wedge q \in P^*(x^\circ)$, which implies the existence of the smallest and the largest equilibrium price vectors.
--
--   This exhibits the conjugacy at the heart of the chapter: commodities correspond to M$^\natural$-convexity, prices to L$^\natural$-convexity. Having a lattice (indeed polyhedral-lattice) structure on the equilibrium price set is of direct algorithmic value: sections 11.4-11.5 use it to justify computing the extreme equilibrium prices by linear/network optimization rather than an undirected search over a possibly disconnected set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.339, Theorem 11.16.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.339, Theorem 11.16

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_MNaturalConvex
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_EquilibriumPriceSet
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_IsLNaturalConvexPolyhedron

namespace DiscreteConvex.EconomicEquilibrium

open DiscreteConvex.MConvexFunctions

/-- Theorem 11.16 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.339). Suppose that utility
functions `Uh` (`h ∈ H`) are M♮-concave and cost functions `Cl` (`l ∈ L`) are M♮-convex, and that
there exists an equilibrium for a total initial endowment `x°`. Then the set `P*(x°)` of all
equilibrium price vectors is an L♮-convex polyhedron. This means, in particular, that
`p, q ∈ P*(x°) ⟹ p ∨ q, p ∧ q ∈ P*(x°)`, which implies the existence of the smallest and the
largest equilibrium price vectors. -/
theorem equilibrium_price_set_l_natural_convex {H K L : Type*} [Fintype H] [Fintype K]
    [Fintype L] [DecidableEq K] (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ)
    (hU : ∀ h, MNaturalConcave (U h)) (hC : ∀ l, MNaturalConvex (C l))
    (x0 : K → ℤ) (hne : (EquilibriumPriceSet U C x0).Nonempty) :
    IsLNaturalConvexPolyhedron (EquilibriumPriceSet U C x0) := by sorry

end DiscreteConvex.EconomicEquilibrium
