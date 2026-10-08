-- Prove2me | Theorems.Thm_ConicQuadIPM_Homogeneous_eq_11
-- name    : ConicQuadIPM.Homogeneous.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:32.173772+00:00
-- url     : https://prove2.me/theorems/7185b16a-d2ac-4c11-b44a-0080888b91d4
-- title:
--   Proof of Lemma 2.1, (11), p. 7 — if κ* > 0 and cᵀx* < 0 then cᵀx* < 0, Ax* = 0, x* ∈ K
-- statement:
--   Let $K \subseteq \mathbb R^n$ be a pointed closed convex cone with dual cone $K_*$, and let $(x^*, \tau^*, y^*, s^*, \kappa^*)$ be a solution of the homogeneous model (7). If $\kappa^* > 0$ and (9) holds, i.e. $c^Tx^* < 0$, then
--   $$c^Tx^* < 0,\qquad Ax^* = 0,\qquad x^* \in K. \qquad (11)$$
--
--   Thus $x^*$ satisfies the hypothesis (6) of Theorem 2.1: it is a certificate that $(D)$ is infeasible.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`, $u^Tv$ is the dot product `u ⬝ᵥ v`, $Ax$ is `A *ᵥ x` and $A^Ty$ is `Aᵀ *ᵥ y`; the paper's first coordinate is index `0`. The standing assumption that $K$ is a pointed closed convex cone is carried as the hypothesis `IsPointedClosedConvexCone K`. The paper's additional assumption that $A$ has full row rank ("for convenience and without loss of generality", p. 4) is not imposed, so the statement is a (harmless) generalization. The hypotheses are exactly those of the page ($\kappa^* > 0$ and (9)); the vanishing of $\tau^*$, which the identity $Ax^* = 0$ requires, is part of what is to be shown and is not assumed.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 7, proof of Lemma 2.1, (11)

import Mathlib
import Definitions.Def_ConicQuadIPM_Homogeneous_Setting

namespace ConicQuadIPM.Homogeneous

open Matrix

/-- Proof of Lemma 2.1, (11), p. 7: for a solution of (7) with `κ* > 0` satisfying (9),
`cᵀx* < 0`, `Ax* = 0` and `x* ∈ K`, so `x*` is a certificate of dual infeasibility. -/
theorem eq_11 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (x : Fin n → ℝ) (τ : ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (κ : ℝ)
    (h : HomFeasible A b c K x τ y s κ) (hκ : 0 < κ) (h9 : c ⬝ᵥ x < 0) :
    c ⬝ᵥ x < 0 ∧ A *ᵥ x = 0 ∧ x ∈ K := by sorry

end ConicQuadIPM.Homogeneous
