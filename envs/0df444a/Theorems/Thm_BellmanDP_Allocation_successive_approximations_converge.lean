-- Prove2me | Theorems.Thm_BellmanDP_Allocation_successive_approximations_converge
-- name    : BellmanDP.Allocation.successive_approximations_converge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T04:59:35.787683+00:00
-- url     : https://prove2.me/theorems/bc0ec502-8240-4635-8b54-ad3aeda5906a
-- title:
--   Chapter I, Theorem 2 — successive approximations from any continuous $f_0$ with $f_0(0)=0$ converge
-- statement:
--   Let $g, h, a, b$ satisfy the hypotheses of Chapter I, Theorem 1: $g$ and $h$ are continuous on $[0,\infty)$ with $g(0)=h(0)=0$; with $m(x) = \max_{0\le y\le x}\max(|g(y)|,|h(y)|)$ and $c=\max(a,b)$, $\sum_{n\ge 0} m(c^n x) < \infty$ for all $x\ge 0$; and $0 \le a,b < 1$. Let $f$ be the solution of
--   $$f(x) = \max_{0\le y\le x}\big[g(y)+h(x-y)+f(ay+b(x-y))\big], \qquad x \ge 0,$$
--   that is continuous at $0$ with $f(0)=0$ (Theorem 1).
--
--   Let $f_0$ be any function continuous on $[0,\infty)$ with $f_0(0)=0$, and define
--   $$f_{N+1}(x) = \max_{0\le y\le x}\big[g(y)+h(x-y)+f_N(ay+b(x-y))\big], \qquad N = 0,1,\dots$$
--   Then $f_N \to f$ uniformly on every finite interval $[0,R]$.
--
--   The theorem says that the value of the infinite process may be computed by iteration from any reasonable starting guess, not only from the particular sequence used in the proof of Theorem 1.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, Theorem 2, p. 16

import Mathlib
import Definitions.Def_BellmanDP_Allocation_Model

namespace BellmanDP.Allocation

/-- Ch. I, Theorem 2, p. 16. Under the hypotheses of Theorem 1, the successive approximations
`f_{N+1}(x) = Max_{0 ≤ y ≤ x} T(f_N, y)` started from any `f₀` continuous on `x ≥ 0` with
`f₀(0) = 0` converge to the solution `f` of Theorem 1 uniformly on every finite interval
`[0, R]`. -/
theorem successive_approximations_converge (g h : ℝ → ℝ) (a b : ℝ)
    (hyp : AllocationHyp g h a b)
    (f₀ : ℝ → ℝ) (hf₀ : ContinuousOn f₀ (Set.Ici 0)) (hf₀0 : f₀ 0 = 0)
    (f : ℝ → ℝ) (hf : IsAllocationSolution g h a b f)
    (hfc : ContinuousWithinAt f (Set.Ici 0) 0) (hf0 : f 0 = 0) :
    ∀ R : ℝ, 0 ≤ R →
      TendstoUniformlyOn (allocIter g h a b f₀) f Filter.atTop (Set.Icc 0 R) := by sorry

end BellmanDP.Allocation
