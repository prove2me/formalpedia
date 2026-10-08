-- Prove2me | Theorems.Thm_ConicQuadIPM_Homogeneous_eq_10
-- name    : ConicQuadIPM.Homogeneous.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:52.610994+00:00
-- url     : https://prove2.me/theorems/c6ded95d-13ae-4c9b-a57d-c737b9fe6d60
-- title:
--   Proof of Lemma 2.1, (10), pp. 6–7 — if κ* > 0 and bᵀy* > 0 then bᵀy* > 0, Aᵀy* + s* = 0, s* ∈ K_*
-- statement:
--   Let $K \subseteq \mathbb R^n$ be a pointed closed convex cone with dual cone $K_*$, and let $(x^*, \tau^*, y^*, s^*, \kappa^*)$ be a solution of the homogeneous model (7). If $\kappa^* > 0$ and (8) holds, i.e. $b^Ty^* > 0$, then
--   $$b^Ty^* > 0,\qquad A^Ty^* + s^* = 0,\qquad s^* \in K_*. \qquad (10)$$
--
--   Thus $(y^*, s^*)$ satisfies the hypothesis (5) of Theorem 2.1: $y^*$ is a Farkas-type certificate that $(P)$ is infeasible.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`, $u^Tv$ is the dot product `u ⬝ᵥ v`, $Ax$ is `A *ᵥ x` and $A^Ty$ is `Aᵀ *ᵥ y`; the paper's first coordinate is index `0`. The standing assumption that $K$ is a pointed closed convex cone is carried as the hypothesis `IsPointedClosedConvexCone K`. The paper's additional assumption that $A$ has full row rank ("for convenience and without loss of generality", p. 4) is not imposed, so the statement is a (harmless) generalization. The hypotheses are exactly those of the page ($\kappa^* > 0$ and (8)); the vanishing of $\tau^*$, which the identity $A^Ty^* + s^* = 0$ requires, is part of what is to be shown and is not assumed.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, pp. 6–7, proof of Lemma 2.1, (10)

import Mathlib
import Definitions.Def_ConicQuadIPM_Homogeneous_Setting

namespace ConicQuadIPM.Homogeneous

open Matrix

/-- Proof of Lemma 2.1, (10), pp. 6–7: for a solution of (7) with `κ* > 0` satisfying (8),
`bᵀy* > 0`, `Aᵀy* + s* = 0` and `s* ∈ K_*`, so `y*` is a Farkas type certificate of primal
infeasibility. -/
theorem eq_10 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (x : Fin n → ℝ) (τ : ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (κ : ℝ)
    (h : HomFeasible A b c K x τ y s κ) (hκ : 0 < κ) (h8 : 0 < b ⬝ᵥ y) :
    0 < b ⬝ᵥ y ∧ Aᵀ *ᵥ y + s = 0 ∧ s ∈ dualCone K := by sorry

end ConicQuadIPM.Homogeneous
