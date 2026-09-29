-- Prove2me | Theorems.Thm_ConeLifts_Factorization_mem_of_liftSpace
-- name    : ConeLifts.Factorization.mem_of_liftSpace
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:46:42.68716+00:00
-- url     : https://prove2.me/theorems/ff36b955-a216-4954-913a-4693e2074a4e
-- title:
--   Theorem 2.4, proof, p. 5 — points of the factorization space lying over $K$ project into $C$
-- statement:
--   Let $C \subseteq \mathbb R^n$ be a convex body, $K \subseteq \mathbb R^m$ a full-dimensional closed convex cone, and $B : \operatorname{ext}(C^\circ) \to K^*$. Let $x \in \mathbb R^n$ and $z \in K$ satisfy
--
--   $$
--   1 - \langle x, y\rangle = \langle z, B(y)\rangle \qquad \text{for all } y \in \operatorname{ext}(C^\circ),
--   $$
--
--   that is, $(x,z)$ lies in the affine space $L$ of the converse half of Theorem 2.4. Then $x \in C$.
--
--   Together with the next milestone this shows that $z \mapsto x_z$ maps $K \cap L_K$ into $C$, the inclusion $\pi(K \cap L_K) \subseteq C$ of the converse half.
--
--   **Formalization Note** $B$ is a total function $\mathbb R^n \to \mathbb R^m$ with $B(y) \in K^*$ required for $y \in \operatorname{ext}(C^\circ)$ only.
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
`B : ext(C°) → K*`. If `x ∈ ℝⁿ` and some `z ∈ K` satisfy `1 - ⟨x, y⟩ = ⟨z, B(y)⟩` for every
extreme point `y` of `C°` (that is, `(x, z) ∈ L`), then `x ∈ (C°)° = C`. -/
theorem mem_of_liftSpace {n m : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (hKint : (interior K).Nonempty)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hB : ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), B y ∈ ConeLifts.Shared.dualCone K)
    (x : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ K)
    (hxz : ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), 1 - ⟪x, y⟫_ℝ = ⟪z, B y⟫_ℝ) :
    x ∈ C := by sorry

end ConeLifts.Factorization
