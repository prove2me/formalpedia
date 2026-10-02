-- Prove2me | Theorems.Thm_DiscreteConvex_Algorithms_base_polyhedron_min_max
-- name    : DiscreteConvex.Algorithms.base_polyhedron_min_max
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T03:26:57.018574+00:00
-- url     : https://prove2.me/theorems/4343b6df-b6e8-4806-baa3-e360829ae424
-- title:
--   Proposition 10.8 -- min-max relation for the base polyhedron
-- statement:
--   **Proposition 10.8** (p.288). For a finite-valued submodular set function $\rho : 2^V \to \mathbb R$, $\max\{x^-(V) : x \in B(\rho)\} = \min\{\rho(X) : X \subseteq V\}$ (Eq. (10.11)). If $\rho$ is integer valued, the maximizer $x$ can be chosen to be an integer vector.
--
--   **Formalization note.** No method or algorithm appears in this statement — it is a structural min-max identity, proved independently of (and, per the book's own remark, an easy consequence of) Edmonds's intersection theorem (chunk 04's `edmonds_intersection_theorem`) — chosen as a milestone precisely because it needs no algorithm-formalization apparatus, unlike this mission's other two items.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, Proposition 10.8.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, Proposition 10.8

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSets_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSets_BasePolyhedron
import Definitions.Def_DiscreteConvex_Algorithms_NegSum
import Definitions.Def_DiscreteConvex_Algorithms_IsIntegerValued

open DiscreteConvex.MConvexSets

namespace DiscreteConvex.Algorithms

/-- Proposition 10.8 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.288). For a
finite-valued submodular set function `ρ : 2^V → R`, `max\{x⁻(V) : x ∈ B(ρ)\} = min\{ρ(X) :
X ⊆ V\}`. If `ρ` is integer valued, the maximizer can be chosen to be an integer vector. -/
theorem base_polyhedron_min_max {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (hfin : ∀ X, ρ X ≠ ⊤) :
    (sSup {v : WithTop ℝ | ∃ x ∈ BasePolyhedron ρ, v = (NegSum x : WithTop ℝ)} =
      Finset.univ.inf ρ) ∧
    (IsIntegerValued ρ →
      ∃ x ∈ BasePolyhedron ρ, (∀ v : V, ∃ n : ℤ, x v = (n : ℝ)) ∧
        (NegSum x : WithTop ℝ) = Finset.univ.inf ρ) := by sorry

end DiscreteConvex.Algorithms
