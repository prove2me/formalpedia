-- Prove2me | Theorems.Thm_ConicQuadIPM_Homogeneous_lemma_2_1
-- name    : ConicQuadIPM.Homogeneous.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:43.409441+00:00
-- url     : https://prove2.me/theorems/affeb8d8-9b20-40a8-9f0e-3d90ac6e6574
-- title:
--   Lemma 2.1, p. 6 — solutions of the homogeneous model (7) are complementary, and give an optimal pair (τ* > 0) or an infeasibility certificate (κ* > 0)
-- statement:
--   Let $A \in \mathbb R^{m\times n}$, $b \in \mathbb R^m$, $c \in \mathbb R^n$, let $K \subseteq \mathbb R^n$ be a pointed closed convex cone with dual cone $K_* = \{s : s^Tx \ge 0\ \forall x \in K\}$, and consider the conic pair $(P)$: $\min\{c^Tx : Ax = b,\ x \in K\}$ and $(D)$: $\max\{b^Ty : A^Ty + s = c,\ s \in K_*\}$. Let $(x^*, \tau^*, y^*, s^*, \kappa^*)$ be any solution of the homogeneous model (7):
--   $$Ax^* - b\tau^* = 0,\quad A^Ty^* + s^* - c\tau^* = 0,\quad -c^Tx^* + b^Ty^* - \kappa^* = 0,\quad x^* \in K,\ \tau^* \ge 0,\ s^* \in K_*,\ \kappa^* \ge 0.$$
--   Then:
--
--   1. (i) $(x^*)^Ts^* + \tau^*\kappa^* = 0$.
--   2. (ii) If $\tau^* > 0$, then $x^*/\tau^*$ is an optimal solution of $(P)$ and $(y^*, s^*)/\tau^*$ is an optimal solution of $(D)$.
--   3. (iii) If $\kappa^* > 0$, then at least one of the strict inequalities $b^Ty^* > 0$ (8) and $c^Tx^* < 0$ (9) holds; if $b^Ty^* > 0$ then $(P)$ is infeasible, and if $c^Tx^* < 0$ then $(D)$ is infeasible.
--
--   The homogeneous model always has the trivial solution, so the lemma is about what a solution with $\tau^* + \kappa^* > 0$ delivers: either a scaled optimal primal–dual pair or a certificate of infeasibility. This is what makes an interior-point method applied to (7) a complete solution method for $(P)$ and $(D)$.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`, $u^Tv$ is the dot product `u ⬝ᵥ v`, $Ax$ is `A *ᵥ x` and $A^Ty$ is `Aᵀ *ᵥ y`; the paper's first coordinate is index `0`. The standing assumption that $K$ is a pointed closed convex cone is carried as the hypothesis `IsPointedClosedConvexCone K`. The paper's additional assumption that $A$ has full row rank ("for convenience and without loss of generality", p. 4) is not imposed, so the statement is a (harmless) generalization. Division by $\tau^*$ is written as scalar multiplication by $(\tau^*)^{-1}$ and is only used under $\tau^* > 0$. Optimality and infeasibility are order and non-existence predicates over all feasible points.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 6, Lemma 2.1 i)–iii) with (8), (9); proof pp. 6–7

import Mathlib
import Definitions.Def_ConicQuadIPM_Homogeneous_Setting

namespace ConicQuadIPM.Homogeneous

open Matrix

/-- Lemma 2.1 (p. 6). Let `(x*, τ*, y*, s*, κ*)` be any solution of the homogeneous model (7).
Then i) `(x*)ᵀs* + τ*κ* = 0`; ii) if `τ* > 0`, `x*/τ*` is optimal for (P) and `(y*, s*)/τ*` is
optimal for (D); iii) if `κ* > 0`, then `bᵀy* > 0` or `cᵀx* < 0`; if `bᵀy* > 0` then (P) is
infeasible, and if `cᵀx* < 0` then (D) is infeasible. -/
theorem lemma_2_1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (x : Fin n → ℝ) (τ : ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (κ : ℝ)
    (h : HomFeasible A b c K x τ y s κ) :
    x ⬝ᵥ s + τ * κ = 0 ∧
    (0 < τ → PrimalOptimal A b c K (τ⁻¹ • x) ∧ DualOptimal A b c K (τ⁻¹ • y) (τ⁻¹ • s)) ∧
    (0 < κ → (0 < b ⬝ᵥ y ∨ c ⬝ᵥ x < 0) ∧ (0 < b ⬝ᵥ y → PrimalInfeasible A b K) ∧
      (c ⬝ᵥ x < 0 → DualInfeasible A c K)) := by sorry

end ConicQuadIPM.Homogeneous
