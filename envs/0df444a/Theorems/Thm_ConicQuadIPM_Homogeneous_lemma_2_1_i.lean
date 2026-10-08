-- Prove2me | Theorems.Thm_ConicQuadIPM_Homogeneous_lemma_2_1_i
-- name    : ConicQuadIPM.Homogeneous.lemma_2_1_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:44.448737+00:00
-- url     : https://prove2.me/theorems/aeaca4a4-71e9-4c8f-90f6-e8a4e3690865
-- title:
--   Lemma 2.1 i), p. 6 — every solution of the homogeneous model (7) satisfies xᵀs + τκ = 0
-- statement:
--   Let $K \subseteq \mathbb R^n$ be a pointed closed convex cone with dual cone $K_*$, and let $(x^*, \tau^*, y^*, s^*, \kappa^*)$ be any solution of the homogeneous model (7):
--   $$Ax^* - b\tau^* = 0,\quad A^Ty^* + s^* - c\tau^* = 0,\quad -c^Tx^* + b^Ty^* - \kappa^* = 0,\quad x^* \in K,\ \tau^* \ge 0,\ s^* \in K_*,\ \kappa^* \ge 0.$$
--   Then the complementarity gap vanishes:
--   $$(x^*)^Ts^* + \tau^*\kappa^* = 0.$$
--
--   In the paper's terminology, every solution of (7) is complementary. This identity drives both other parts of Lemma 2.1.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`, $u^Tv$ is the dot product `u ⬝ᵥ v`, $Ax$ is `A *ᵥ x` and $A^Ty$ is `Aᵀ *ᵥ y`; the paper's first coordinate is index `0`. The standing assumption that $K$ is a pointed closed convex cone is carried as the hypothesis `IsPointedClosedConvexCone K`. The paper's additional assumption that $A$ has full row rank ("for convenience and without loss of generality", p. 4) is not imposed, so the statement is a (harmless) generalization.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 6, Lemma 2.1 i)

import Mathlib
import Definitions.Def_ConicQuadIPM_Homogeneous_Setting

namespace ConicQuadIPM.Homogeneous

open Matrix

/-- Lemma 2.1 i) (p. 6): every solution of the homogeneous model (7) is complementary,
`(x*)ᵀs* + τ*κ* = 0`. -/
theorem lemma_2_1_i {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (x : Fin n → ℝ) (τ : ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (κ : ℝ)
    (h : HomFeasible A b c K x τ y s κ) :
    x ⬝ᵥ s + τ * κ = 0 := by sorry

end ConicQuadIPM.Homogeneous
