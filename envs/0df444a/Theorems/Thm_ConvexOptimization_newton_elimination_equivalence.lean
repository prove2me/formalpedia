-- Prove2me | Theorems.Thm_ConvexOptimization_newton_elimination_equivalence
-- name    : ConvexOptimization.newton_elimination_equivalence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T15:28:41.615225+00:00
-- url     : https://prove2.me/theorems/f4f561d9-a628-42e0-9d98-cf360dadbb75
-- title:
--   Eliminated Newton solves the constrained KKT system
-- statement:
--   **Newton's method commutes with elimination of equality constraints** (B&V §10.2.3): the Newton step of the reduced problem, mapped back, solves the KKT system of the constrained problem.
--
--   Consider minimizing a twice differentiable $f : \mathbb{R}^n \to \mathbb{R}$ subject to the affine constraints $\langle a_j, x\rangle = b_j$, $j = 1,\dots,p$. Let $F : \mathbb{R}^{q} \to \mathbb{R}^{n}$ be linear and parametrize the constraint null space,
--
--   $$\operatorname{ran} F \;=\; \{\, v \in \mathbb{R}^n : \langle a_j, v\rangle = 0 \ \text{ for all } j \,\},$$
--
--   let $\hat{x}$ be arbitrary, put $x = F z + \hat{x}$, and let $\Delta z \in \mathbb{R}^{q}$ solve the reduced Newton system of $z \mapsto f(Fz + \hat x)$, stated variationally as $\langle \nabla^2 f(x)\, F\Delta z,\, Fw\rangle = -\langle \nabla f(x),\, Fw\rangle$ for every $w \in \mathbb{R}^{q}$. Then $\Delta x = F\Delta z$ solves the equality-constrained Newton KKT system (10.12):
--
--   $$\exists\, \nu \in \mathbb{R}^{p} : \quad \nabla f(x) + \nabla^2 f(x)\,\Delta x + \sum_{j=1}^{p} \nu_j\, a_j = 0, \qquad \langle a_j, \Delta x\rangle = 0 \ \ (j = 1,\dots,p),$$
--
--   where $\nu$ is the vector of dual variables associated with the equality constraints.
--
--   The two natural ways of running Newton's method on an equality-constrained problem — eliminate the constraints and run the unconstrained method, or keep them and solve the larger KKT system — therefore produce the same step. That is what allows the convergence theory of the unconstrained case to be transferred verbatim to the constrained one, and it makes the choice between the two implementations a purely numerical matter.
--
--   **Formalization Note** $F$ is a continuous linear map `EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin n)` and the null-space property is an iff between the constraint equations and membership in `Set.range F`. The reduced Newton system is given in the weak form quantified over test vectors $w$, which is equivalent to $F^{T}\nabla^2 f\,F\,\Delta z = -F^{T}\nabla f$ without introducing adjoints. The conclusion asserts existence of the multiplier $\nu$, matching the KKT system rather than a particular formula for it. Source: B&V §10.2.3, pp. 526–527.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 526-527, §10.2.3 eq. (10.11) (the Newton step of the eliminated problem solves the KKT system defining the equality-constrained Newton step)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.newton_elimination_equivalence {n q p : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x, HasFDerivAt g (H x) x)
    (a : Fin p → EuclideanSpace ℝ (Fin n))
    (F : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin n))
    -- F parametrizes the constraint null space: ran F = {v | Av = 0}
    (hF : ∀ v : EuclideanSpace ℝ (Fin n),
      (∀ j, ⟪a j, v⟫ = 0) ↔ v ∈ Set.range F)
    (xhat : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin q))
    (Δz : EuclideanSpace ℝ (Fin q))
    -- Δz solves the reduced Newton system Fᵀ H F Δz = −Fᵀ g at x = F z + x̂:
    (hΔz : ∀ w : EuclideanSpace ℝ (Fin q),
      ⟪H (F z + xhat) (F Δz), F w⟫ = -⟪g (F z + xhat), F w⟫) :
    -- then Δx = F Δz solves the KKT system (10.12): stationarity with some ν,
    -- and primal feasibility of the step direction (A Δx = 0):
    (∃ ν : Fin p → ℝ,
      g (F z + xhat) + H (F z + xhat) (F Δz) + ∑ j, ν j • a j = 0) ∧
    ∀ j, ⟪a j, F Δz⟫ = 0 := by
  sorry
