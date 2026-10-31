-- Prove2me | Theorems.Thm_DualRCD_strong_duality_slater
-- name    : DualRCD.strong_duality_slater
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:53.81199+00:00
-- url     : https://prove2.me/theorems/ae363456-26c7-4080-b2c3-1f3b61b2e5ef
-- title:
--   (11) — strong duality and dual attainment under Slater's condition
-- statement:
--   Let $g:\mathbb R^n\to\mathbb R$ be $1$-strongly convex with $L$-Lipschitz gradient, and let $X_1,\dots,X_m\subseteq\mathbb R^n$ be closed convex sets satisfying Slater's condition (6). Then:
--
--   1. the dual problem (10) has an optimal solution, that is $Y^*\ne\emptyset$;
--   2. the primal problem (3) has an optimal solution $x^*$, and $g(x^*)=-d^*$;
--   3. for every $y^*\in Y^*$, the point
--   $$
--   x^*=\nabla g^*\Big(-\sum_{j=1}^my^*_j\Big)
--   $$
--   is an optimal solution of the primal problem.
--
--   This connects the primal and dual problems, and it provides the nonempty set $Y^*$ onto which the convergence proof of RCD projects.
--
--   **Formalization Note.** The point $\nabla g^*(-\sum_jy^*_j)$ is written as the arg max of $\langle-\sum_jy^*_j,\cdot\rangle-g$.
--
--   Differences from the source:
--   - generalization: 0 < σ < L, that is 1 < L since σ = 1 → any real L; reason: the paper's §6 applies the theory with σ = L = 1, so the strict inequality is not what the paper uses; every instance of the source is an instance of the Lean statement
--   - reading: strong duality holds [31], for any dual optimal solution y* → the conclusion includes Y* ≠ ∅; reason: Rockafellar's Slater theorem [31] includes attainment, and the paper goes on to use dual optimal solutions and the projection onto Y*
--   - encoding: g* = −d*, with g* the primal optimal value of (8) → a primal optimal xs exists and dStar g X = −g xs; reason: the notation g* is overloaded in the paper; it is the conjugate in (10)
--   - encoding: x* = ∇g*(−Σ_{j=1}^M y*_j) → every arg max of ⟨−Σ_j ys j, ·⟩ − g is primal optimal; reason: M is m (typo), and the arg max is ∇g*, p.15
--   - encoding: the inequality pair of p.4 with ∇g → IsStronglyConvexGrad and IsSmoothGrad, each with Differentiable ℝ g and Mathlib's gradient; reason: Lean's gradient is 0 where g is not differentiable, so differentiability is stated
--   - encoding: ℝ^{mn} with the Euclidean norm → PiLp 2 of EuclideanSpace ℝ (Fin n) (DualSpace n m); reason: Lean convention; ‖y‖² = Σᵢ‖yᵢ‖² is the paper's norm
--   - encoding: d : ℝ^{mn} → ℝ on its domain, with d* = min_y d(y) → dualFn and dStar valued in EReal, with dStar the infimum; reason: supp is +∞ off its domain; under Slater's condition d takes no value −∞ and d* is finite
--   - encoding: blocks 1, …, m, Slater with i ≤ r and i ≥ r + 1 → Fin m, with i.val < r and r ≤ i.val; reason: Lean indexes from 0; same condition
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, §3.1, p.7, display (11)

import Mathlib
import Definitions.Def_DualRCD_IsStronglyConvexGrad
import Definitions.Def_DualRCD_IsSmoothGrad
import Definitions.Def_DualRCD_IsSlater
import Definitions.Def_DualRCD_Ystar
import Definitions.Def_DualRCD_dStar
import Definitions.Def_DualRCD_IsConjMaximizer
import Definitions.Def_DualRCD_IsPrimalOptimal

open scoped RealInnerProductSpace

namespace DualRCD

/-- Strong duality under Slater's condition (Necoara & Fercoq, arXiv:1911.06014v1, §3.1, p.7, display
(11)). If the closed convex sets `Xᵢ` satisfy Slater's condition (6), then the dual optimum is
attained (`Y* ≠ ∅`), the primal problem (3) has an optimal solution `x*` with `g(x*) = −d*`, and for
every `y* ∈ Y*` the point `∇g*(−Σⱼ y*ⱼ)` is primal optimal.

**Formalization Note.** `g*` in the paper's "`g* = −d*`" is the primal optimal value of (8), here
`g x*`, not the conjugate. "`Y* ≠ ∅`" is read into "strong duality" (Rockafellar's theorem [31]
includes attainment, and the sentence continues with "any dual optimal solution"). `r` ranges over
`0 ≤ r ≤ m`, as in Definition 2. -/
theorem strong_duality_slater {n m : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hg : IsStronglyConvexGrad 1 g) (hgL : IsSmoothGrad L g)
    (X : Fin m → Set (EuclideanSpace ℝ (Fin n)))
    (hXc : ∀ i, IsClosed (X i)) (hXv : ∀ i, Convex ℝ (X i))
    (r : ℕ) (hS : IsSlater X r) :
    (Ystar g X : Set (DualSpace n m)).Nonempty ∧
      (∃ xs, IsPrimalOptimal g X xs ∧ dStar g X = ((-g xs : ℝ) : EReal)) ∧
      ∀ ys ∈ (Ystar g X : Set (DualSpace n m)), ∀ xs,
        IsConjMaximizer g (-∑ j, ys j) xs → IsPrimalOptimal g X xs := by sorry

end DualRCD
