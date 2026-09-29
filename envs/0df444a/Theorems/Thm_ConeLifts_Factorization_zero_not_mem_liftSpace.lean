-- Prove2me | Theorems.Thm_ConeLifts_Factorization_zero_not_mem_liftSpace
-- name    : ConeLifts.Factorization.zero_not_mem_liftSpace
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:46:01.940369+00:00
-- url     : https://prove2.me/theorems/65fe9741-0edc-45be-9f6d-5d2976c0ee43
-- title:
--   Theorem 2.4, proof, p. 5 — the projection $L_K$ of the factorization space does not contain $0$
-- statement:
--   Let $C \subseteq \mathbb R^n$ be a convex body and $B : \operatorname{ext}(C^\circ) \to \mathbb R^m$ any map. Consider the affine space
--
--   $$
--   L = \{\, (x,z) \in \mathbb R^n \times \mathbb R^m : 1 - \langle x, y\rangle = \langle z, B(y)\rangle \ \ \forall y \in \operatorname{ext}(C^\circ) \,\}
--   $$
--
--   and its coordinate projection $L_K = \{z : \exists x,\ (x,z) \in L\}$ to $\mathbb R^m$. Then $0 \notin L_K$; equivalently, no $x \in \mathbb R^n$ has $\langle x, y\rangle = 1$ for every extreme point $y$ of $C^\circ$.
--
--   In the converse half of Theorem 2.4 this is what allows the map $z \mapsto x_z$ to be extended to a linear map $\pi$.
--
--   **Formalization Note** $B$ is an arbitrary function $\mathbb R^n \to \mathbb R^m$; only its values on $\operatorname{ext}(C^\circ)$ enter. $L_K$ is written out as a set comprehension.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, pp. 4-5, Theorem 2.4 (proof)

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Shared_polar

open scoped InnerProductSpace

namespace ConeLifts.Factorization

/-- Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, Theorem 2.4, proof, p. 5: for any map
`B : ext(C°) → ℝᵐ`, the coordinate projection `L_K` to `ℝᵐ` of the affine space
`L = {(x, z) ∈ ℝⁿ × ℝᵐ : 1 - ⟨x, y⟩ = ⟨z, B(y)⟩ ∀ y ∈ ext(C°)}` does not contain the origin. -/
theorem zero_not_mem_liftSpace {n m : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :
    (0 : EuclideanSpace ℝ (Fin m)) ∉
      {z : EuclideanSpace ℝ (Fin m) | ∃ x : EuclideanSpace ℝ (Fin n),
        ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), 1 - ⟪x, y⟫_ℝ = ⟪z, B y⟫_ℝ} := by sorry

end ConeLifts.Factorization
