-- Prove2me | Theorems.Thm_BellmanDP_Allocation_allocation_equation_exists_unique
-- name    : BellmanDP.Allocation.allocation_equation_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T14:14:10.639505+00:00
-- url     : https://prove2.me/theorems/8a9637c5-6c5d-4a03-8bfc-4b66ce32f405
-- title:
--   Chapter I, Theorem 1 — existence and uniqueness for the allocation equation
-- statement:
--   Let $g, h : [0,\infty) \to \mathbb{R}$ and $a, b$ satisfy:
--   1. $g$ and $h$ are continuous for $x \ge 0$, and $g(0) = h(0) = 0$;
--   2. with $m(x) = \max_{0\le y\le x}\max(|g(y)|,|h(y)|)$ and $c = \max(a,b)$, $\sum_{n=0}^{\infty} m(c^n x) < \infty$ for all $x \ge 0$;
--   3. $0 \le a < 1$ and $0 \le b < 1$.
--
--   Then the equation
--   $$f(x) = \max_{0 \le y \le x}\big[ g(y) + h(x-y) + f(ay + b(x-y)) \big], \qquad x \ge 0,$$
--   has a solution $f$ that is continuous at $x = 0$ with $f(0) = 0$; this solution is continuous for all $x \ge 0$; and any other solution that is continuous at $x=0$ with value $0$ there coincides with $f$ on $[0,\infty)$.
--
--   The equation describes the total return of an infinite-stage process in which a resource $x$ is split between two activities with returns $g$ and $h$ and depreciation factors $a$ and $b$. The theorem is what makes "the solution" of this equation meaningful: without the side condition at $0$ uniqueness fails (for $g=h=0$ every constant, and the indicator of $(0,\infty)$, are solutions).
--
--   **Formalization Note** Functions are `ℝ → ℝ`, and all hypotheses and conclusions concern $x \ge 0$ only; continuity at $0$ is one-sided (within $[0,\infty)$) and uniqueness is equality on $[0,\infty)$. The maximum in the equation is required to be attained for every $x\ge 0$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, Theorem 1, p. 12 (equation (8.1), p. 11)

import Mathlib
import Definitions.Def_BellmanDP_Allocation_Model

namespace BellmanDP.Allocation

/-- Bellman, *Dynamic Programming*, Ch. I, Theorem 1, p. 12. Under (1a)–(1c) the equation (8.1)
`f(x) = Max_{0 ≤ y ≤ x} [g(y) + h(x − y) + f(ay + b(x − y))]` has a solution on `x ≥ 0` that is
continuous at `x = 0` with value `0` there; it is continuous for all `x ≥ 0`; and every solution
continuous at `0` with value `0` there coincides with it on `x ≥ 0`. -/
theorem allocation_equation_exists_unique (g h : ℝ → ℝ) (a b : ℝ)
    (hyp : AllocationHyp g h a b) :
    ∃ f : ℝ → ℝ, IsAllocationSolution g h a b f ∧
      ContinuousWithinAt f (Set.Ici 0) 0 ∧ f 0 = 0 ∧
      ContinuousOn f (Set.Ici 0) ∧
      ∀ F : ℝ → ℝ, IsAllocationSolution g h a b F →
        ContinuousWithinAt F (Set.Ici 0) 0 → F 0 = 0 →
        ∀ x : ℝ, 0 ≤ x → F x = f x := by sorry

end BellmanDP.Allocation
