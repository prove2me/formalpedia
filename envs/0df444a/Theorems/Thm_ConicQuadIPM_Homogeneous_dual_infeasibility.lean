-- Prove2me | Theorems.Thm_ConicQuadIPM_Homogeneous_dual_infeasibility
-- name    : ConicQuadIPM.Homogeneous.dual_infeasibility
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:00.121103+00:00
-- url     : https://prove2.me/theorems/98bf4e30-48fa-4929-92d4-9b5a6236268a
-- title:
--   Theorem 2.1, Dual infeasibility (6), p. 5 — x ∈ K, Ax = 0, cᵀx < 0 certifies that (D) is infeasible
-- statement:
--   Let $K \subseteq \mathbb R^n$ be a pointed closed convex cone with dual cone $K_*$, and let $(D)$ be the problem $\max\{b^Ty : A^Ty + s = c,\ s \in K_*\}$. If there is an $x$ with
--   $$x \in K,\qquad Ax = 0,\qquad c^Tx < 0,$$
--   then $(D)$ has no feasible pair $(y, s)$.
--
--   Such an $x$ is a certificate of dual infeasibility; Lemma 2.1 iii) shows that a solution of the homogeneous model with $\kappa > 0$ and $c^Tx < 0$ produces one.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`, $u^Tv$ is the dot product `u ⬝ᵥ v`, $Ax$ is `A *ᵥ x` and $A^Ty$ is `Aᵀ *ᵥ y`; the paper's first coordinate is index `0`. The standing assumption that $K$ is a pointed closed convex cone is carried as the hypothesis `IsPointedClosedConvexCone K`. The paper's additional assumption that $A$ has full row rank ("for convenience and without loss of generality", p. 4) is not imposed, so the statement is a (harmless) generalization. The right-hand side $b$ plays no role and is not a parameter.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 5, Theorem 2.1 (Dual infeasibility), (6)

import Mathlib
import Definitions.Def_ConicQuadIPM_Homogeneous_Setting

namespace ConicQuadIPM.Homogeneous

open Matrix

/-- Theorem 2.1, Dual infeasibility (6) (p. 5): if some `x ∈ K` has `Ax = 0` and `cᵀx < 0`,
then (D) is infeasible. -/
theorem dual_infeasibility {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (hcert : ∃ x : Fin n → ℝ, x ∈ K ∧ A *ᵥ x = 0 ∧ c ⬝ᵥ x < 0) :
    DualInfeasible A c K := by sorry

end ConicQuadIPM.Homogeneous
