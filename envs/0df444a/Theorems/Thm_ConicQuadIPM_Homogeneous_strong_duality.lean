-- Prove2me | Theorems.Thm_ConicQuadIPM_Homogeneous_strong_duality
-- name    : ConicQuadIPM.Homogeneous.strong_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:33.549984+00:00
-- url     : https://prove2.me/theorems/1085e3d1-76ba-473c-9c2e-e1efe344bbaa
-- title:
--   Theorem 2.1, Strong duality, p. 4 — under strict feasibility and boundedness, (x, y, s) is optimal iff feasible with cᵀx − bᵀy = xᵀs = 0
-- statement:
--   Let $K \subseteq \mathbb R^n$ be a pointed closed convex cone with dual cone $K_*$, and consider $(P)$: $\min\{c^Tx : Ax = b,\ x \in K\}$ and $(D)$: $\max\{b^Ty : A^Ty + s = c,\ s \in K_*\}$. Suppose that
--
--   1. $(P)$ is strictly feasible (some $x$ with $Ax = b$ lies in $\operatorname{int}(K)$) and its objective $c^Tx$ is bounded below on its feasible set, **or**
--   2. $(D)$ is strictly feasible (some $(y,s)$ with $A^Ty + s = c$ has $s \in \operatorname{int}(K_*)$) and its objective $b^Ty$ is bounded above on its feasible set.
--
--   Then for all $x \in \mathbb R^n$, $y \in \mathbb R^m$, $s \in \mathbb R^n$: $x$ is optimal for $(P)$ and $(y,s)$ is optimal for $(D)$ if and only if $x$ is primal feasible, $(y, s)$ is dual feasible, and
--   $$c^Tx - b^Ty = x^Ts = 0.$$
--
--   Under a Slater-type condition on one side the duality gap closes, so optimal pairs are exactly the feasible pairs with zero complementarity gap.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`, $u^Tv$ is the dot product `u ⬝ᵥ v`, $Ax$ is `A *ᵥ x` and $A^Ty$ is `Aᵀ *ᵥ y`; the paper's first coordinate is index `0`. The standing assumption that $K$ is a pointed closed convex cone is carried as the hypothesis `IsPointedClosedConvexCone K`. The paper's additional assumption that $A$ has full row rank ("for convenience and without loss of generality", p. 4) is not imposed, so the statement is a (harmless) generalization. "Its optimal objective value is bounded" is read as: the objective is bounded below (for $(P)$), resp. above (for $(D)$), on the feasible set. "$(x,y,s)$ is an optimal solution" is read as: $x$ is optimal for $(P)$ and $(y,s)$ is optimal for $(D)$. Interiors are topological interiors in $\mathbb R^n$, as on p. 4. The paper cites this part ([11]) and does not prove it.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 4, Theorem 2.1 (Strong duality), with strict feasibility as defined on p. 4

import Mathlib
import Definitions.Def_ConicQuadIPM_Homogeneous_Setting

namespace ConicQuadIPM.Homogeneous

open Matrix

/-- Theorem 2.1, Strong duality (p. 4): if (P) is strictly feasible and its objective is bounded
below on its feasible set, or (D) is strictly feasible and its objective is bounded above on its
feasible set, then `(x, y, s)` is an optimal solution (`x` optimal for (P), `(y, s)` optimal for (D))
if and only if `cᵀx − bᵀy = xᵀs = 0`, `x` is primal feasible and `(y, s)` is dual feasible. -/
theorem strong_duality {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (hreg : (PrimalStrictlyFeasible A b K ∧
        BddBelow ((fun x => c ⬝ᵥ x) '' {x | PrimalFeasible A b K x})) ∨
      (DualStrictlyFeasible A c K ∧
        BddAbove ((fun y => b ⬝ᵥ y) '' {y | ∃ s, DualFeasible A c K y s})))
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) :
    (PrimalOptimal A b c K x ∧ DualOptimal A b c K y s) ↔
      (c ⬝ᵥ x - b ⬝ᵥ y = x ⬝ᵥ s ∧ x ⬝ᵥ s = 0 ∧
        PrimalFeasible A b K x ∧ DualFeasible A c K y s) := by sorry

end ConicQuadIPM.Homogeneous
