-- Prove2me | Theorems.Thm_BellmanDP_Allocation_policy_space_approximation_monotone
-- name    : BellmanDP.Allocation.policy_space_approximation_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T05:14:50.758625+00:00
-- url     : https://prove2.me/theorems/b8ba1911-74a2-4961-b39d-3df0f23bfb85
-- title:
--   Chapter I, Theorem 3 — approximation in policy space converges monotonely
-- statement:
--   Assume the hypotheses of Chapter I, Theorem 1 (continuity of $g,h$ on $[0,\infty)$, $g(0)=h(0)=0$, $\sum_{n}m(c^n x)<\infty$ with $c=\max(a,b)$, and $0\le a,b<1$), and let $f$ be the solution of (8.1) that is continuous at $0$ with $f(0)=0$.
--
--   Let $y_0$ be any function continuous on $[0,\infty)$ with $0 \le y_0(x) \le x$, and let $f_0$ be the return of the stationary policy $y_0$, i.e. the solution of
--   $$f_0(x) = g(y_0(x)) + h(x-y_0(x)) + f_0\big(a y_0(x) + b(x - y_0(x))\big)$$
--   given by the series of total stage returns along the trajectory of $y_0$. Define
--   $$f_{N+1}(x) = \max_{0\le y\le x}\big[g(y)+h(x-y)+f_N(ay+b(x-y))\big], \qquad N=0,1,2,\dots$$
--   Then:
--   1. the sequence is monotone: $f_N(x) \le f_{N+1}(x)$ for all $N$ and all $x\ge 0$;
--   2. $f_N \to f$ uniformly on every finite interval $[0,R]$.
--
--   Starting the iteration from the return of a policy, rather than from an arbitrary function, guarantees that every iterate improves on the previous one.
--
--   **Formalization Note** The book writes "converges uniformly"; the uniformity is stated on every finite interval $[0,R]$, as in Theorem 2 and in the series argument (11.10) that the proof uses.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, Theorem 3, p. 18

import Mathlib
import Definitions.Def_BellmanDP_Allocation_Model
import Definitions.Def_BellmanDP_Allocation_PolicyReturn

namespace BellmanDP.Allocation

/-- Ch. I, Theorem 3, p. 18. Let `y₀` be continuous on `x ≥ 0` with `0 ≤ y₀(x) ≤ x`, and let
`f₀` be the return of the stationary policy `y₀` (the solution (11.10) of `f₀(x) = T(f₀, y₀(x))`).
Under the hypotheses of Theorem 1 the successive approximations
`f_{N+1}(x) = Max_{0 ≤ y ≤ x} T(f_N, y)` are monotone nondecreasing in `N` on `x ≥ 0` and converge
to the solution `f` of Theorem 1 uniformly on every finite interval `[0, R]`. -/
theorem policy_space_approximation_monotone (g h : ℝ → ℝ) (a b : ℝ)
    (hyp : AllocationHyp g h a b)
    (y₀ : ℝ → ℝ) (hy₀ : ContinuousOn y₀ (Set.Ici 0))
    (hy₀r : ∀ x : ℝ, 0 ≤ x → 0 ≤ y₀ x ∧ y₀ x ≤ x)
    (f : ℝ → ℝ) (hf : IsAllocationSolution g h a b f)
    (hfc : ContinuousWithinAt f (Set.Ici 0) 0) (hf0 : f 0 = 0) :
    (∀ N : ℕ, ∀ x : ℝ, 0 ≤ x →
        allocIter g h a b (policyReturn g h a b y₀) N x ≤
          allocIter g h a b (policyReturn g h a b y₀) (N + 1) x) ∧
      ∀ R : ℝ, 0 ≤ R →
        TendstoUniformlyOn (allocIter g h a b (policyReturn g h a b y₀)) f Filter.atTop
          (Set.Icc 0 R) := by sorry

end BellmanDP.Allocation
