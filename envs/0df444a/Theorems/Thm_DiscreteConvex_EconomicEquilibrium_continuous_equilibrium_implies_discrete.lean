-- Prove2me | Theorems.Thm_DiscreteConvex_EconomicEquilibrium_continuous_equilibrium_implies_discrete
-- name    : DiscreteConvex.EconomicEquilibrium.continuous_equilibrium_implies_discrete
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T05:18:09.678036+00:00
-- url     : https://prove2.me/theorems/30fd2ae0-9ec8-49d2-8a58-9a959cdae4c8
-- title:
--   Theorem 11.14 -- a continuous equilibrium yields a discrete one
-- statement:
--   **Theorem 11.14** (p.338). Suppose that utility functions $U_h$ ($h \in H$) are M$^\natural$-concave and cost functions $C_l$ ($l \in L$) are M$^\natural$-convex. If the derived continuous economy has an equilibrium satisfying (11.33), (11.34), (11.14), and (11.12) for a total initial endowment $x^\circ \in \mathbb Z^K_+$, there exists an equilibrium of indivisible commodities for $x^\circ$ satisfying (11.9), (11.10), (11.14), and (11.12).
--
--   This is the constructive half of the existence argument for the general economy (with both consumers and producers): it embeds the discrete model into a continuous one via the concave/convex closures $\hat U_h$, $\hat C_l$, where classical fixed-point/compactness arguments for continuous economies apply, and then transports a continuous equilibrium back down to a genuine discrete one. The book stresses this transport is *not* a general phenomenon — section 11.2's example shows a continuous equilibrium can fail to correspond to any discrete one — but is peculiar to the M$^\natural$-concavity/convexity hypotheses.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.338, Theorem 11.14.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.338, Theorem 11.14

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_MNaturalConvex
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_IsEquilibrium
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_IsContEquilibrium

namespace DiscreteConvex.EconomicEquilibrium

open DiscreteConvex.MConvexFunctions

/-- Theorem 11.14 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.338). Suppose that utility
functions `Uh` (`h ∈ H`) are M♮-concave and cost functions `Cl` (`l ∈ L`) are M♮-convex. If the
derived continuous economy has an equilibrium satisfying (11.33), (11.34), (11.14), and (11.12)
for a total initial endowment `x° ∈ Zᴷ₊`, there exists an equilibrium of indivisible commodities
for `x°` satisfying (11.9), (11.10), (11.14), and (11.12). -/
theorem continuous_equilibrium_implies_discrete {H K L : Type*} [Fintype H] [Fintype K]
    [Fintype L] [DecidableEq K] (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ)
    (hU : ∀ h, MNaturalConcave (U h)) (hC : ∀ l, MNaturalConvex (C l))
    (x0 : K → ℤ) (hx0 : ∀ k, 0 ≤ x0 k)
    (xc : H → (K → ℝ)) (yc : L → (K → ℝ)) (pc : K → ℝ)
    (hcont : IsContEquilibrium U C x0 xc yc pc) :
    ∃ (x : H → (K → ℤ)) (y : L → (K → ℤ)) (p : K → ℝ), IsEquilibrium U C x0 x y p := by sorry

end DiscreteConvex.EconomicEquilibrium
