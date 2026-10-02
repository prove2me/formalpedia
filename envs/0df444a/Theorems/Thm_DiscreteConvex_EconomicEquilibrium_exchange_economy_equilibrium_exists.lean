-- Prove2me | Theorems.Thm_DiscreteConvex_EconomicEquilibrium_exchange_economy_equilibrium_exists
-- name    : DiscreteConvex.EconomicEquilibrium.exchange_economy_equilibrium_exists
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T05:19:36.00208+00:00
-- url     : https://prove2.me/theorems/bb13dcd8-5b8a-4807-88a1-86787dacc52a
-- title:
--   Theorem 11.13 -- existence of equilibrium for an exchange economy (goal)
-- statement:
--   **Theorem 11.13** (p.337), the goal theorem of this mission. Consider an exchange economy (no producers) with agents indexed by $H$, and suppose that $U_h$ ($h \in H$) are nondecreasing M$^\natural$-concave functions with $\operatorname{dom} U_h$ bounded. Then there exists an equilibrium $((x_h \mid h \in H), p)$ for every total initial endowment $x^\circ \in \bigcap_{h \in H} \operatorname{dom} U_h$.
--
--   This is the chapter's central result: a genuine existence theorem for a discrete (indivisible-goods) general-equilibrium model, proved *by* discrete convexity. Section 11.2 ("Difficulty with Indivisibility") exhibits an exchange economy, with utilities that are submodular and concave-extensible but not M$^\natural$-concave, that has *no* equilibrium at all for some initial endowments — so the M$^\natural$-concavity hypothesis is not a mild regularity condition but exactly the property that makes existence possible for indivisible goods, in sharp contrast to the classical divisible-goods theory where mere concavity and continuity suffice.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337, Theorem 11.13.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337, Theorem 11.13

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_Nondecreasing
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_UDom
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_BoundedSet
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_IsEquilibrium

namespace DiscreteConvex.EconomicEquilibrium

/-- Theorem 11.13 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.337), the goal theorem of this
mission: existence of equilibrium in an exchange economy. Consider an exchange economy (no
producers, `L = PEmpty`) with agents indexed by `H`, and suppose that `Uh` (`h ∈ H`) are
nondecreasing M♮-concave functions with `dom Uh` bounded. Then there exists an equilibrium
`((xh | h ∈ H), p)` for every total initial endowment `x° ∈ ⋂_{h ∈ H} dom Uh`. -/
theorem exchange_economy_equilibrium_exists {H K : Type*} [Fintype H] [Fintype K] [DecidableEq K]
    (U : H → (K → ℤ) → WithBot ℝ) (hU : ∀ h, MNaturalConcave (U h))
    (hUnd : ∀ h, Nondecreasing (U h)) (hUb : ∀ h, BoundedSet (UDom (U h)))
    (x0 : K → ℤ) (hx0 : ∀ h, x0 ∈ UDom (U h)) :
    ∃ (x : H → (K → ℤ)) (p : K → ℝ),
      IsEquilibrium U (fun l : PEmpty => l.elim) x0 x (fun l : PEmpty => l.elim) p := by sorry

end DiscreteConvex.EconomicEquilibrium
