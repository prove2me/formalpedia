-- Prove2me | Theorems.Thm_ConeLifts_Factorization_slater_certificate
-- name    : ConeLifts.Factorization.slater_certificate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:45:26.928927+00:00
-- url     : https://prove2.me/theorems/588f0663-0b85-442e-969e-29459d794748
-- title:
--   Theorem 2.4, proof, p. 4 — strong conic duality: $1 = \min\{\langle w_0,z\rangle : z-\pi^*(c)\in K^*,\ z\in L_0^\perp\}$, attained
-- statement:
--   Let $n \ge 1$, let $C \subseteq \mathbb R^n$ be a convex body and $K \subseteq \mathbb R^m$ a full-dimensional closed convex cone. Suppose $C = \pi(K \cap L)$ for a linear map $\pi : \mathbb R^m \to \mathbb R^n$ and an affine subspace $L = w_0 + L_0$ ($L_0$ its direction) with $w_0 \in L \cap \operatorname{int} K$. Let $c$ be an extreme point of $C^\circ$ and $\pi^*$ the adjoint of $\pi$. Then
--
--   $$
--   1 = \min\{\, \langle w_0, z\rangle \;:\; z - \pi^*(c) \in K^*,\ z \in L_0^{\perp} \,\},
--   $$
--
--   and the minimum is attained: every feasible $z$ has $\langle w_0, z\rangle \ge 1$, and some feasible $z$ has $\langle w_0, z\rangle = 1$.
--
--   This is the dual certificate from which the proof of Theorem 2.4 builds the factor $B(c) = z - \pi^*(c) \in K^*$. The underlying primal problem is $\max\{\langle \pi^*(c), w\rangle : w \in K \cap L\}$, whose value is $1$, and $w_0$ is a Slater point for it.
--
--   **Formalization Note** The paper first writes the dual with a full-row-rank matrix $M$ whose kernel is $L_0$ and then substitutes $z = M^{\mathsf T} y$; the statement here is the second (substituted) form, which is the one the construction uses. $L_0^\perp$ is `L.directionᗮ` and $\pi^*$ is `LinearMap.adjoint π`. The minimum is stated with `IsLeast`, so attainment is part of the claim. $n \ge 1$ is needed for the same reason as in the previous milestone.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 4, Theorem 2.4 (proof)

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_Factorization_IsClosedConvexCone
import Definitions.Def_ConeLifts_Shared_dualCone

open scoped InnerProductSpace

namespace ConeLifts.Factorization

/-- Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, Theorem 2.4, proof, p. 4 (the strong-duality
step). Let `C = π(K ∩ L)` with `L = w₀ + L₀` an affine subspace, `π` linear and
`w₀ ∈ int(K)`, and let `c` be an extreme point of `C°`. Then
`1 = min {⟨w₀, z⟩ : z - π*(c) ∈ K*, z ∈ L₀^⊥}` with the minimum attained. Here `L₀` is
`L.direction`, `π*` is the adjoint `LinearMap.adjoint π`, and `K*` is `dualCone K`.
`1 ≤ n` is the paper's implicit full-dimensionality of `C`. -/
theorem slater_certificate {n m : ℕ} (hn : 1 ≤ n)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (hKint : (interior K).Nonempty)
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin m)))
    (π : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (w₀ : EuclideanSpace ℝ (Fin m)) (hw₀L : w₀ ∈ L) (hw₀K : w₀ ∈ interior K)
    (hCπ : C = π '' (K ∩ (L : Set (EuclideanSpace ℝ (Fin m)))))
    (c : EuclideanSpace ℝ (Fin n)) (hc : c ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C)) :
    IsLeast {t : ℝ | ∃ z ∈ L.directionᗮ,
        z - LinearMap.adjoint π c ∈ ConeLifts.Shared.dualCone K ∧ t = ⟪w₀, z⟫_ℝ} 1 := by sorry

end ConeLifts.Factorization
