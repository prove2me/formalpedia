-- Prove2me | Theorems.Thm_DiscreteConvex_AlgorithmsB_base_polyhedron_min_max
-- name    : DiscreteConvex.AlgorithmsB.base_polyhedron_min_max
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T03:58:55.638594+00:00
-- url     : https://prove2.me/theorems/5747d496-770b-4913-9d28-97be7909bf2d
-- title:
--   Proposition 10.8 -- base_polyhedron_min_max
-- statement:
--   **Proposition 10.8** (p.288). The min-max relation $\max\{x^-(V)\mid x\in B(\rho)\}=\min\{\rho(X)\mid X\subseteq V\}$; if $\rho$ is integer valued the maximizer can be chosen integral.
--
--   **Not in this chunk's own `BRIEF.md` table** — found by direct reading, the min-max theorem (an Edmonds-intersection-theorem consequence) underlying the whole of section 10.2's algorithmic framework.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, Proposition 10.8.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, Proposition 10.8

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_Submodular
import Definitions.Def_DiscreteConvex_AlgorithmsB_MinRho
import Definitions.Def_DiscreteConvex_AlgorithmsB_BasePolyhedronR
import Definitions.Def_DiscreteConvex_AlgorithmsB_NegPart

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.8 (p.288). The min-max relation `max{x⁻(V) | x∈B(ρ)} = min{ρ(X) | X⊆V}`; if
`ρ` is integer valued the maximizer can be chosen integral. -/
theorem base_polyhedron_min_max (rho : Finset V → ℤ) (hrho : Submodular rho) :
    IsGreatest {t : ℝ | ∃ x : V → ℝ, BasePolyhedronR rho x ∧ t = ∑ v, NegPart x v}
      ((MinRho rho : ℝ)) ∧
    ∃ x : V → ℤ, (∀ X : Finset V, ∑ v ∈ X, (x v : ℝ) ≤ (rho X : ℝ)) ∧
      (∑ v, (x v : ℝ) = (rho Finset.univ : ℝ)) ∧
      (∑ v, NegPart (fun v => (x v : ℝ)) v = (MinRho rho : ℝ)) := by sorry

end DiscreteConvex.AlgorithmsB
