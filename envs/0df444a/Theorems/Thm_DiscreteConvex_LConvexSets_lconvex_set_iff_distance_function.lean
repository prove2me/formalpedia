-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexSets_lconvex_set_iff_distance_function
-- name    : DiscreteConvex.LConvexSets.lconvex_set_iff_distance_function
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:37:13.174989+00:00
-- url     : https://prove2.me/theorems/e3ffc549-3dc5-4336-a54a-827d111eca4b
-- title:
--   Theorem 5.5 -- L-convex sets correspond to integer distance functions
-- statement:
--   **Theorem 5.5** (p.125). A nonempty set $D \subseteq \mathbb Z^V$ is L-convex if and only if $D = D(\gamma) \cap \mathbb Z^V$ for some integer-valued distance function $\gamma$ satisfying the triangle inequality, establishing a one-to-one correspondence between L-convex sets and integer-valued distance functions with the triangle inequality.
--
--   **Formalization Note.** As with chunk 04's Theorem 4.15, the book additionally names the mutually inverse maps $\Phi$ (Eq. (5.8)) and $\Psi$ realizing this correspondence; this mission states the iff itself (an existential $\gamma$) and does not construct $\Phi$ as a separate object.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.125, Theorem 5.5.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.125, Theorem 5.5

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSets_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexSets_DistanceFunction
import Definitions.Def_DiscreteConvex_LConvexSets_TriangleInequality
import Definitions.Def_DiscreteConvex_LConvexSets_AdmissiblePotentials
import Definitions.Def_DiscreteConvex_LConvexSets_IsIntegerValuedDist

namespace DiscreteConvex.LConvexSets

/-- Theorem 5.5 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.125). A nonempty set
`D ⊆ Zⱽ` is L-convex if and only if `D = D(γ) ∩ Zⱽ` for some integer-valued distance function
`γ` satisfying the triangle inequality, establishing a one-to-one correspondence between
L-convex sets and integer-valued distance functions with the triangle inequality. -/
theorem lconvex_set_iff_distance_function {V : Type*} [Fintype V] [DecidableEq V]
    (D : Set (V → ℤ)) (hD : D.Nonempty) :
    LConvexSet D ↔
      ∃ γ : V → V → WithTop ℝ, DistanceFunction γ ∧ TriangleInequality γ ∧
        IsIntegerValuedDist γ ∧
        D = {p : V → ℤ | (fun v => (p v : ℝ)) ∈ AdmissiblePotentials γ} := by sorry

end DiscreteConvex.LConvexSets
