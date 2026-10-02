-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSets_edmonds_intersection_theorem
-- name    : DiscreteConvex.MConvexSets.edmonds_intersection_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:19:08.999757+00:00
-- url     : https://prove2.me/theorems/2b1ab7e1-be3d-453f-b7e2-b863e229a8f0
-- title:
--   Theorem 4.18 -- Edmonds's intersection theorem
-- statement:
--   **Theorem 4.18** (Edmonds, p.112). For submodular set functions $\rho_1, \rho_2 \in S[\mathbb R]$,
--
--   $$\max\{x(V) : x \in P(\rho_1) \cap P(\rho_2)\} = \min\{\rho_1(X) + \rho_2(V\setminus X) : X \subseteq V\},$$
--
--   both sides attained. Moreover, if $\rho_1, \rho_2$ are integer valued, $P(\rho_1) \cap P(\rho_2)$ is an **integral polyhedron** and the maximum is attained at an integer point. The real max-min equality alone is ordinary LP duality with no discrete content; the integrality clause is the chapter's own combinatorial contribution and is never dropped from the goal even though a milestone-level treatment could prove the real case first.
--
--   **Formalization Note.** Both sides of the max-min equality, and the objective/RHS values, are compared in `EReal` (via the embedding `ToEReal`) so that `+∞` values of $\rho_1,\rho_2$ are handled uniformly; `IsGreatest`/`IsLeast` state that each extremum is genuinely attained, not merely a supremum/infimum.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.112, Theorem 4.18.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.112, Theorem 4.18

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSets_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSets_SubmodularPolyhedron
import Definitions.Def_DiscreteConvex_MConvexSets_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSets_IsIntegralPolyhedron
import Definitions.Def_DiscreteConvex_MConvexSets_ToEReal

namespace DiscreteConvex.MConvexSets

/-- Theorem 4.18 (Edmonds's intersection theorem; Murota, *Discrete Convex Analysis*, SIAM
2003, p.112). For submodular set functions `ρ1, ρ2 ∈ S[R]`,
`max\{x(V) : x ∈ P(ρ1) ∩ P(ρ2)\} = min\{ρ1(X) + ρ2(V∖X) : X ⊆ V\}`, both sides attained.
Moreover, if `ρ1, ρ2` are integer valued, `P(ρ1) ∩ P(ρ2)` is an integral polyhedron and the
maximum is attained at an integer point. -/
theorem edmonds_intersection_theorem {V : Type*} [Fintype V] [DecidableEq V]
    (ρ1 ρ2 : Finset V → WithTop ℝ) (hρ1 : SubmodularSetFunction ρ1)
    (hρ2 : SubmodularSetFunction ρ2) :
    (∃ m : EReal,
        IsGreatest ((fun x : V → ℝ => ToEReal ((∑ v, x v : ℝ) : WithTop ℝ)) ''
          (SubmodularPolyhedron ρ1 ∩ SubmodularPolyhedron ρ2)) m ∧
        IsLeast ((fun X : Finset V => ToEReal (ρ1 X) + ToEReal (ρ2 Xᶜ)) ''
          (Set.univ : Set (Finset V))) m) ∧
    (IsIntegerValued ρ1 → IsIntegerValued ρ2 →
      IsIntegralPolyhedron (SubmodularPolyhedron ρ1 ∩ SubmodularPolyhedron ρ2) ∧
      ∃ x ∈ SubmodularPolyhedron ρ1 ∩ SubmodularPolyhedron ρ2, (∀ v, ∃ k : ℤ, x v = (k : ℝ)) ∧
        IsGreatest ((fun y : V → ℝ => ToEReal ((∑ v, y v : ℝ) : WithTop ℝ)) ''
          (SubmodularPolyhedron ρ1 ∩ SubmodularPolyhedron ρ2))
          (ToEReal ((∑ v, x v : ℝ) : WithTop ℝ))) := by sorry

end DiscreteConvex.MConvexSets
