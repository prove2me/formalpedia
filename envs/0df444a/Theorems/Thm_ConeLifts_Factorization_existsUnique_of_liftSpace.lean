-- Prove2me | Theorems.Thm_ConeLifts_Factorization_existsUnique_of_liftSpace
-- name    : ConeLifts.Factorization.existsUnique_of_liftSpace
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:47:17.352718+00:00
-- url     : https://prove2.me/theorems/e2053e42-3bea-4d8a-8dc0-fc6cc8a7248a
-- title:
--   Theorem 2.4, proof, p. 5 — each $z \in K\cap L_K$ has a unique $x_z$ with $(x_z, z) \in L$
-- statement:
--   Let $C \subseteq \mathbb R^n$ be a convex body, $K \subseteq \mathbb R^m$ a full-dimensional closed convex cone, $B : \operatorname{ext}(C^\circ) \to K^*$, and
--
--   $$
--   L = \{\, (x,z) : 1 - \langle x, y\rangle = \langle z, B(y)\rangle \ \ \forall y \in \operatorname{ext}(C^\circ) \,\}, \qquad L_K = \{z : \exists x,\ (x,z)\in L\}.
--   $$
--
--   For every $z \in K \cap L_K$ there is exactly one $x_z \in \mathbb R^n$ with $(x_z, z) \in L$.
--
--   This makes $z \mapsto x_z$ a well-defined map on $K \cap L_K$, which the converse half of Theorem 2.4 extends to the linear map $\pi$ of the lift.
--
--   **Formalization Note** Membership $z \in L_K$ is the hypothesis that some $x$ satisfies the defining equations; the conclusion is Lean's `∃!`.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 5, Theorem 2.4 (proof)

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_Factorization_IsClosedConvexCone
import Definitions.Def_ConeLifts_Shared_dualCone

open scoped InnerProductSpace

namespace ConeLifts.Factorization

/-- Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, Theorem 2.4, proof, p. 5: let
`B : ext(C°) → K*` and `L = {(x, z) : 1 - ⟨x, y⟩ = ⟨z, B(y)⟩ ∀ y ∈ ext(C°)}`. For each
`z ∈ K ∩ L_K` (i.e. `z ∈ K` with `(x, z) ∈ L` for some `x`) there is a unique `x_z ∈ ℝⁿ` with
`(x_z, z) ∈ L`. -/
theorem existsUnique_of_liftSpace {n m : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (hKint : (interior K).Nonempty)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hB : ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), B y ∈ ConeLifts.Shared.dualCone K)
    (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ K)
    (hzL : ∃ x : EuclideanSpace ℝ (Fin n),
      ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), 1 - ⟪x, y⟫_ℝ = ⟪z, B y⟫_ℝ) :
    ∃! x : EuclideanSpace ℝ (Fin n),
      ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), 1 - ⟪x, y⟫_ℝ = ⟪z, B y⟫_ℝ := by sorry

end ConeLifts.Factorization
