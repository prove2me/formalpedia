-- Prove2me | Theorems.Thm_ConicQuadIPM_Homogeneous_weak_duality
-- name    : ConicQuadIPM.Homogeneous.weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:31.302042+00:00
-- url     : https://prove2.me/theorems/3472c435-9b5a-4d45-8bbc-1e9c351d2f15
-- title:
--   Theorem 2.1, Weak duality, p. 4 — cᵀx − bᵀy = xᵀs ≥ 0 for feasible x and (y, s)
-- statement:
--   Consider the conic primal–dual pair $(P)$: $\min\{c^Tx : Ax = b,\ x \in K\}$ and $(D)$: $\max\{b^Ty : A^Ty + s = c,\ s \in K_*\}$, where $K \subseteq \mathbb R^n$ is a pointed closed convex cone and $K_*$ its dual cone.
--
--   If $x$ is feasible for $(P)$ and $(y, s)$ is feasible for $(D)$, then
--   $$c^Tx - b^Ty = x^Ts \ge 0.$$
--
--   The difference $c^Tx - b^Ty$ is the duality gap and $x^Ts$ the complementarity gap; weak duality says the two coincide on feasible points and are nonnegative, so every dual objective value bounds every primal objective value from below.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`, $u^Tv$ is the dot product `u ⬝ᵥ v`, $Ax$ is `A *ᵥ x` and $A^Ty$ is `Aᵀ *ᵥ y`; the paper's first coordinate is index `0`. The standing assumption that $K$ is a pointed closed convex cone is carried as the hypothesis `IsPointedClosedConvexCone K`. The paper's additional assumption that $A$ has full row rank ("for convenience and without loss of generality", p. 4) is not imposed, so the statement is a (harmless) generalization.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 4, Theorem 2.1 (Weak duality)

import Mathlib
import Definitions.Def_ConicQuadIPM_Homogeneous_Setting

namespace ConicQuadIPM.Homogeneous

open Matrix

/-- Theorem 2.1, Weak duality (p. 4): for `x` feasible for (P) and `(y, s)` feasible for (D),
`cᵀx − bᵀy = xᵀs ≥ 0`. -/
theorem weak_duality {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ)
    (hx : PrimalFeasible A b K x) (hys : DualFeasible A c K y s) :
    c ⬝ᵥ x - b ⬝ᵥ y = x ⬝ᵥ s ∧ 0 ≤ x ⬝ᵥ s := by sorry

end ConicQuadIPM.Homogeneous
