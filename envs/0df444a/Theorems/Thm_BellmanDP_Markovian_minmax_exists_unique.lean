-- Prove2me | Theorems.Thm_BellmanDP_Markovian_minmax_exists_unique
-- name    : BellmanDP.Markovian.minmax_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T21:58:11.001271+00:00
-- url     : https://prove2.me/theorems/7acecfb3-73d3-4b1b-be2a-3ceadbbe9a5f
-- title:
--   Chapter XI, Theorem 4 — existence and uniqueness for $dx/dt=\max_p\min_q[A(p,q,t)x+b(p,q,t)]$
-- statement:
--   For each row $i = 1, \dots, N$ let two players choose $p_i$ and $q_i$ from admissible sets, and let $a_{ij}(p_i, q_i, t)$, $b_i(p_i, q_i, t)$ be real coefficients. Fix $T > 0$ and assume:
--
--   1. (2a) for fixed $x$ and $t$ the max-min equals the min-max, row by row: $V_i(t,x) = \max_p \min_q [A(p,q,t)x + b(p,q,t)]_i = \min_q \max_p [\dots]_i$, both extrema attained;
--   2. (2b) $\max_S \|A(p,q,t)\|,\ \max_S \|b(p,q,t)\| \le f(t)$ for $t \ge 0$, where $\int_0^T f(t)\, dt < \infty$ and the norms are sums of absolute values;
--   3. $t \mapsto V(t,x)$ is measurable for each $x$.
--
--   Then the equation
--   $$\frac{dx}{dt} = \max_p \min_q \big[A(p,q,t)x + b(p,q,t)\big] = \min_q \max_p [\dots], \qquad x(0) = c,$$
--   has a unique solution in $0 \le t \le T$ satisfying the equation almost everywhere (continuous, with $x(t) = c + \int_0^t V(s,x(s))\,ds$), and it is the uniform limit on $[0,T]$ of the successive approximations $x_0 = c$, $x_{n+1}(t) = c + \int_0^t V(s, x_n(s))\, ds$.
--
--   This is the two-person (game) version of Theorem 1.
--
--   **Formalization Note** As in § 3, the max-min is taken element by element, each row with its own players' choices. Measurability of $t \mapsto V(t,x)$ is not stated in the book and is added so that the integrals are meaningful.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter XI, Theorem 4, p. 332

import Mathlib
import Definitions.Def_BellmanDP_Markovian_Continuous

namespace BellmanDP.Markovian

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. XI, Theorem 4, p. 332. Let row `i`'s players choose
`p ∈ SP i`, `q ∈ SQ i`, and let `V(t, x)` be, row by row, the common value
`Max_p Min_q [A(p, q, t) x + b(p, q, t)] = Min_q Max_p […]` (condition (2a)). Assume (2b):
`Max_S ‖A(p, q, t)‖, Max_S ‖b(p, q, t)‖ ≤ f(t)` for `t ≥ 0` with `∫_0^T f(t) dt < ∞`, and that
`t ↦ V(t, x)` is measurable for each `x`. Then `dx/dt = V(t, x)`, `x(0) = c`, has a unique
solution on `0 ≤ t ≤ T` satisfying the equation almost everywhere (in integral form), and it is
the uniform limit on `[0, T]` of the successive approximations (12.3). -/
theorem minmax_exists_unique {N : ℕ} {P Q : Fin N → Type*}
    (A : (i : Fin N) → P i → Q i → ℝ → Fin N → ℝ) (b : (i : Fin N) → P i → Q i → ℝ → ℝ)
    (SP : (i : Fin N) → Set (P i)) (SQ : (i : Fin N) → Set (Q i))
    (V : ℝ → (Fin N → ℝ) → Fin N → ℝ) (hV : IsRowwiseSaddleValue A b SP SQ V)
    (hVmeas : ∀ x : Fin N → ℝ, Measurable fun t => V t x)
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Icc 0 T))
    (hA : ∀ t : ℝ, 0 ≤ t → ∀ p ∈ Set.pi Set.univ SP, ∀ q ∈ Set.pi Set.univ SQ,
      ∑ i, ∑ j, |A i (p i) (q i) t j| ≤ f t)
    (hb : ∀ t : ℝ, 0 ≤ t → ∀ p ∈ Set.pi Set.univ SP, ∀ q ∈ Set.pi Set.univ SQ,
      ∑ i, |b i (p i) (q i) t| ≤ f t)
    (c : Fin N → ℝ) :
    ∃ x : ℝ → Fin N → ℝ, IsIntegralSolutionOn V c T x ∧
      (∀ z : ℝ → Fin N → ℝ, IsIntegralSolutionOn V c T z → Set.EqOn z x (Set.Icc 0 T)) ∧
      TendstoUniformlyOn (picardIter V c) x Filter.atTop (Set.Icc 0 T) := by sorry

end BellmanDP.Markovian
