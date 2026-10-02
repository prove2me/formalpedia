-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexityB_prop_3_14_bipartite_matching_potentials
-- name    : DiscreteConvex.IntegralConvexityB.prop_3_14_bipartite_matching_potentials
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:04:35.403718+00:00
-- url     : https://prove2.me/theorems/10806ccf-3b1b-4fb7-a226-641d661217d0
-- title:
--   Proposition 3.14 -- potentials certify a minimum-weight perfect matching
-- statement:
--   A perfect matching and dual potentials realizing complementary slackness certify minimum weight, with an explicit value formula.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.109, Proposition 3.14.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.109, Proposition 3.14

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPerfectMatchingBij
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsMinWeightMatching
import Definitions.Def_DiscreteConvex_IntegralConvexityB_MatchingWeight

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.109, Proposition 3.14, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- **Proposition 3.14.** Let `G = (Vp, Vm; E)` be a bipartite graph with a perfect matching,
and `c` a cost with `c(u,v) < +∞ ↔ (u,v) ∈ E`. Then there exist a potential `p̂` and a perfect
matching `σ` such that `c(u, σ u) + p̂(u) - p̂(σ u) = 0` and `c(u,v) + p̂(u) - p̂(v) ≥ 0` for all
`u, v`; `σ` is a minimum-weight perfect matching, and its weight equals
`∑_u (p̂(σ u) - p̂(u))`. -/
theorem prop_3_14_bipartite_matching_potentials {Vp Vm : Type*} [Fintype Vp] [Fintype Vm]
    [DecidableEq Vp] [DecidableEq Vm] (E : Set (Vp × Vm)) (c : Vp × Vm → WithTop ℝ)
    (hc : ∀ u v, c (u, v) < ⊤ ↔ (u, v) ∈ E) (sigma0 : Vp ≃ Vm)
    (hsigma0 : IsPerfectMatchingBij E sigma0) :
    ∃ (pp : Vp → ℝ) (pm : Vm → ℝ) (sigma : Vp ≃ Vm),
      (∀ u, c (u, sigma u) + (pp u : WithTop ℝ) - (pm (sigma u) : WithTop ℝ) = 0) ∧
        (∀ u v, c (u, v) + (pp u : WithTop ℝ) - (pm v : WithTop ℝ) ≥ 0) ∧
        IsMinWeightMatching E c sigma ∧
        MatchingWeight c sigma = ((∑ u, (pm (sigma u) - pp u) : ℝ) : WithTop ℝ) := by sorry

end DiscreteConvex.IntegralConvexityB
