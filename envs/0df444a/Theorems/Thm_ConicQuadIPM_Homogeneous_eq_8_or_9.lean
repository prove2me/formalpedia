-- Prove2me | Theorems.Thm_ConicQuadIPM_Homogeneous_eq_8_or_9
-- name    : ConicQuadIPM.Homogeneous.eq_8_or_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:03.459617+00:00
-- url     : https://prove2.me/theorems/713d7a21-579b-4f94-9d18-3e6116cbee3f
-- title:
--   Proof of Lemma 2.1, p. 6 — if κ* > 0 then bᵀy* > 0 (8) or cᵀx* < 0 (9)
-- statement:
--   Let $K \subseteq \mathbb R^n$ be a pointed closed convex cone with dual cone $K_*$, and let $(x^*, \tau^*, y^*, s^*, \kappa^*)$ be a solution of the homogeneous model (7) (see Lemma 2.1 i)). If $\kappa^* > 0$, then at least one of the strict inequalities
--   $$b^Ty^* > 0 \quad (8) \qquad\text{or}\qquad c^Tx^* < 0 \quad (9)$$
--   holds.
--
--   This is the first claim of Lemma 2.1 iii); it comes from the third equation of (7), which reads $-c^Tx^* + b^Ty^* = \kappa^*$.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`, $u^Tv$ is the dot product `u ⬝ᵥ v`, $Ax$ is `A *ᵥ x` and $A^Ty$ is `Aᵀ *ᵥ y`; the paper's first coordinate is index `0`. The standing assumption that $K$ is a pointed closed convex cone is carried as the hypothesis `IsPointedClosedConvexCone K`. The paper's additional assumption that $A$ has full row rank ("for convenience and without loss of generality", p. 4) is not imposed, so the statement is a (harmless) generalization.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 6, proof of Lemma 2.1 (first display), with (8) and (9)

import Mathlib
import Definitions.Def_ConicQuadIPM_Homogeneous_Setting

namespace ConicQuadIPM.Homogeneous

open Matrix

/-- Proof of Lemma 2.1, p. 6: for a solution of (7) with `κ* > 0`, at least one of the strict
inequalities (8) `bᵀy* > 0` and (9) `cᵀx* < 0` holds. -/
theorem eq_8_or_9 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (x : Fin n → ℝ) (τ : ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (κ : ℝ)
    (h : HomFeasible A b c K x τ y s κ) (hκ : 0 < κ) :
    0 < b ⬝ᵥ y ∨ c ⬝ᵥ x < 0 := by sorry

end ConicQuadIPM.Homogeneous
