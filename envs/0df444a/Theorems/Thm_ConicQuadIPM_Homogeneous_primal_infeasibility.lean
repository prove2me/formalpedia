-- Prove2me | Theorems.Thm_ConicQuadIPM_Homogeneous_primal_infeasibility
-- name    : ConicQuadIPM.Homogeneous.primal_infeasibility
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:24.339535+00:00
-- url     : https://prove2.me/theorems/f62644eb-c672-4f7b-93b7-2130c2cffcc8
-- title:
--   Theorem 2.1, Primal infeasibility (5), p. 4 — s ∈ K_*, Aᵀy + s = 0, bᵀy > 0 certifies that (P) is infeasible
-- statement:
--   Let $K \subseteq \mathbb R^n$ be a pointed closed convex cone with dual cone $K_*$, and let $(P)$ be the problem $\min\{c^Tx : Ax = b,\ x \in K\}$. If there is a pair $(y, s)$ with
--   $$s \in K_*,\qquad A^Ty + s = 0,\qquad b^Ty > 0,$$
--   then $(P)$ has no feasible point.
--
--   Such a $(y,s)$ is a Farkas-type certificate of primal infeasibility; Lemma 2.1 iii) shows that a solution of the homogeneous model with $\kappa > 0$ and $b^Ty > 0$ produces one.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`, $u^Tv$ is the dot product `u ⬝ᵥ v`, $Ax$ is `A *ᵥ x` and $A^Ty$ is `Aᵀ *ᵥ y`; the paper's first coordinate is index `0`. The standing assumption that $K$ is a pointed closed convex cone is carried as the hypothesis `IsPointedClosedConvexCone K`. The paper's additional assumption that $A$ has full row rank ("for convenience and without loss of generality", p. 4) is not imposed, so the statement is a (harmless) generalization. The display (5) prints $b^Ty^* > 0$; the star is a typographical slip for the bound variable $y$, and the Lean states $b^Ty > 0$. The objective $c$ plays no role and is not a parameter.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 4, Theorem 2.1 (Primal infeasibility), (5)

import Mathlib
import Definitions.Def_ConicQuadIPM_Homogeneous_Setting

namespace ConicQuadIPM.Homogeneous

open Matrix

/-- Theorem 2.1, Primal infeasibility (5) (p. 4): if some `(y, s)` has `s ∈ K_*`,
`Aᵀy + s = 0` and `bᵀy > 0`, then (P) is infeasible. -/
theorem primal_infeasibility {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (hcert : ∃ (y : Fin m → ℝ) (s : Fin n → ℝ),
      s ∈ dualCone K ∧ Aᵀ *ᵥ y + s = 0 ∧ 0 < b ⬝ᵥ y) :
    PrimalInfeasible A b K := by sorry

end ConicQuadIPM.Homogeneous
