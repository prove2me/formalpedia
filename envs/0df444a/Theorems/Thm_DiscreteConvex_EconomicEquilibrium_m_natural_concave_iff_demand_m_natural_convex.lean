-- Prove2me | Theorems.Thm_DiscreteConvex_EconomicEquilibrium_m_natural_concave_iff_demand_m_natural_convex
-- name    : DiscreteConvex.EconomicEquilibrium.m_natural_concave_iff_demand_m_natural_convex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T05:08:12.578972+00:00
-- url     : https://prove2.me/theorems/60852206-8c3a-4531-93fd-efdabd7f7f7e
-- title:
--   Theorem 11.7 -- M$^\natural$-concavity via M$^\natural$-convexity of demand sets
-- statement:
--   **Theorem 11.7** (p.332). For a function $U : \mathbb Z^K \to \mathbb R \cup \{-\infty\}$ with a bounded nonempty effective domain, $U$ is M$^\natural$-concave if and only if $\arg\max U[-p]$ is an M$^\natural$-convex set for each $p \in \mathbb R^K$.
--
--   A more economically legible characterization than Theorem 11.4: it connects the abstract exchange-axiom definition of M$^\natural$-concavity to the structure of the demand sets consumers actually optimize over, and (as the book discusses immediately afterward) is the bridge to the gross substitutes property of Kelso-Crawford and Gul-Stacchetti for set functions.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.332, Theorem 11.7.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.332, Theorem 11.7

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_DemandSet
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_IsMNaturalConvexSet
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_UDom
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_BoundedSet

namespace DiscreteConvex.EconomicEquilibrium

/-- Theorem 11.7 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.332). For a function
`U : Zᴷ → R ∪ {−∞}` with a bounded nonempty effective domain, `U` is M♮-concave if and only if
`arg max U[−p]` is an M♮-convex set for each `p ∈ Rᴷ`. -/
theorem m_natural_concave_iff_demand_m_natural_convex {K : Type*} [Fintype K] [DecidableEq K]
    (U : (K → ℤ) → WithBot ℝ) (hU : (UDom U).Nonempty) (hUb : BoundedSet (UDom U)) :
    MNaturalConcave U ↔ ∀ p : K → ℝ, IsMNaturalConvexSet (DemandSet U p) := by sorry

end DiscreteConvex.EconomicEquilibrium
