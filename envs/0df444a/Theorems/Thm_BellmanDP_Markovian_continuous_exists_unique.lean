-- Prove2me | Theorems.Thm_BellmanDP_Markovian_continuous_exists_unique
-- name    : BellmanDP.Markovian.continuous_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T21:57:54.12949+00:00
-- url     : https://prove2.me/theorems/5dfcc8c1-4d28-4c4e-90f5-2107e75e34d5
-- title:
--   Chapter XI, Theorem 1 — existence and uniqueness for $dx/dt=\max_q[A(q,t)x+b(q,t)]$
-- statement:
--   For each row $i = 1, \dots, N$ let $S_i$ be the set of admissible values of the row's parameter, and let $a_{ij}(q_i, t)$, $b_i(q_i, t)$ be real coefficients. Suppose there is a function $f$, integrable over every finite interval $[0,T]$, with
--   $$\|A(q,t)\| = \sum_{i,j} |a_{ij}(q_i,t)| \le f(t), \qquad \|b(q,t)\| = \sum_i |b_i(q_i,t)| \le f(t)$$
--   for every admissible $q = (q_1,\dots,q_N)$ and $t \ge 0$. Suppose the maximum of $A(q,t)x + b(q,t)$ over $q$ is attained, row by row, for every $t$ and $x$, and write $F(t,x)$ for it; assume $t \mapsto F(t,x)$ is measurable for each $x$. Consider
--   $$\frac{dx}{dt} = \max_q \big[A(q,t)x + b(q,t)\big], \qquad x(0) = c .$$
--   Then:
--
--   1. there is a function $x$ that solves the equation almost everywhere on every interval $[0,T]$, i.e. $x$ is continuous and $x(t) = c + \int_0^t F(s, x(s))\, ds$;
--   2. any solution on an interval $[0, S]$ coincides with $x$ there;
--   3. the successive approximations $x_0 = c$, $x_{n+1}(t) = c + \int_0^t \max_q[A(q,s)x_n(s) + b(q,s)]\, ds$ converge to $x$ uniformly on every $[0,T]$.
--
--   This is the basic well-posedness result for the continuous Markovian decision process of the chapter.
--
--   **Formalization Note** The admissible $q$ of the book are functions of $t$; since the maximization is pointwise, the statement uses the pointwise sets $S_i$ and the integral of the pointwise maximum (the book's (4.2)). Measurability of $t \mapsto F(t,x)$ is not stated in the book and is added so that the integrals are meaningful.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter XI, Theorem 1, p. 321 (with Eqs. (5.1)-(5.3), (5.10), pp. 321-323)

import Mathlib
import Definitions.Def_BellmanDP_Markovian_Continuous

namespace BellmanDP.Markovian

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. XI, Theorem 1, p. 321. Let row `i`'s parameter range
over `S i`, with `‖A(q, t)‖, ‖b(q, t)‖ ≤ f(t)` for every admissible joint `q` and `t ≥ 0` (norms
(3.5): sums of absolute values), `f` integrable over every `[0, T]`, and let
`F(t, x) = Max_q [A(q, t) x + b(q, t)]` (row by row, maximum attained). Assume `t ↦ F(t, x)` is
measurable for each `x`. Then `dx/dt = F(t, x)`, `x(0) = c`, has a solution satisfying the
equation almost everywhere (in integral form) on every `[0, T]`; any solution on an interval
`[0, S']` coincides with it there; and the successive approximations (5.3) converge to it
uniformly on every `[0, T]`. -/
theorem continuous_exists_unique {N : ℕ} {Q : Fin N → Type*}
    (A : (i : Fin N) → Q i → ℝ → Fin N → ℝ) (b : (i : Fin N) → Q i → ℝ → ℝ)
    (S : (i : Fin N) → Set (Q i)) (f : ℝ → ℝ)
    (hf : ∀ T : ℝ, IntegrableOn f (Set.Icc 0 T))
    (hA : ∀ t : ℝ, 0 ≤ t → ∀ q ∈ Set.pi Set.univ S, ∑ i, ∑ j, |A i (q i) t j| ≤ f t)
    (hb : ∀ t : ℝ, 0 ≤ t → ∀ q ∈ Set.pi Set.univ S, ∑ i, |b i (q i) t| ≤ f t)
    (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) (hF : IsRowwiseMax A b S F)
    (hFmeas : ∀ x : Fin N → ℝ, Measurable fun t => F t x) (c : Fin N → ℝ) :
    ∃ x : ℝ → Fin N → ℝ,
      (∀ T : ℝ, 0 < T → IsIntegralSolutionOn F c T x) ∧
      (∀ S' : ℝ, 0 < S' → ∀ z : ℝ → Fin N → ℝ, IsIntegralSolutionOn F c S' z →
        Set.EqOn z x (Set.Icc 0 S')) ∧
      (∀ T : ℝ, 0 < T → TendstoUniformlyOn (picardIter F c) x Filter.atTop (Set.Icc 0 T)) := by sorry

end BellmanDP.Markovian
