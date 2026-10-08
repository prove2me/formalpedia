-- Prove2me | Theorems.Thm_DatkoDelayWave_BoundaryDelay_delay_stability_trichotomy
-- name    : DatkoDelayWave.BoundaryDelay.delay_stability_trichotomy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:01:03.043027+00:00
-- url     : https://prove2.me/theorems/3730200e-c116-4f9e-b2ac-0bfda981c5a7
-- title:
--   The stability trichotomy of the delayed boundary-damped wave equation at the critical gain k = (1−K)/(1+K), K = e^{−2a}
-- statement:
--   Let $a \ge 0$, $k \ge 0$ and $K = e^{-2a}$. Consider the damped wave equation $u_{tt} - u_{xx} + 2au_t + a^2u = 0$ on $0 < x < 1$ with $u(0,t) = 0$ and the delayed boundary feedback $u_x(1,t) = -k\,u_t(1,t-\varepsilon)$, $\varepsilon > 0$, and let $\sigma(a,k,\varepsilon)$ be its spectrum. Then:
--
--   1. If $0 < k < (1-K)/(1+K)$, for each $\varepsilon > 0$ there is $\beta(\varepsilon) > 0$ such that $\sigma(a,k,\varepsilon) \subseteq \{\operatorname{Re}\omega \le -\beta\}$.
--   2. If $k = (1-K)/(1+K)$ and $k > 0$, for each $\varepsilon > 0$ the spectrum lies in $\{\operatorname{Re}\omega < 0\}$, but there is a countable set $R \subseteq (0,\infty)$, dense in $(0,\infty)$, such that for each $\varepsilon \in R$ some sequence $(\omega_n)$ in the spectrum has
--   $$
--   \lim_{n\to\infty}\operatorname{Re}\omega_n = 0 .
--   $$
--   3. If $k > (1-K)/(1+K)$, there is an open set $D \subseteq (0,\infty)$, dense in $(0,\infty)$, such that for each $\varepsilon \in D$ the system admits an exponentially unstable classical solution ($|u(x_0,t)| \ge ce^{\gamma t}$ for some $\gamma, c > 0$, $x_0 \in (0,1)$ and all $t \ge 0$).
--
--   The undelayed system is uniformly exponentially stable whenever $a^2 + k^2 > 0$; the theorem shows that delays destroy this robustly exactly when the gain exceeds $(1-K)/(1+K)$.
--
--   **Formalization Note** In part 2 the hypothesis $k > 0$ is the paper's standing "$k > 0$" (p. 152); without it the part is false at $a = 0$. Part 1 is vacuous at $a = 0$. The spectrum is the set of eigenvalues of the problem on p. 154 (not the zero set of $h$); "countably dense" and "dense open in $(0,\infty)$" are read relative to $(0,\infty)$; "exponentially unstable solution" is read as pointwise exponential growth of a $C^2$ complex-valued classical solution.
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), p. 153, THEOREM (i)–(iii) (proof pp. 154–155)

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

namespace DatkoDelayWave.BoundaryDelay

theorem delay_stability_trichotomy (a k : ℝ) (ha : 0 ≤ a) (hk : 0 ≤ k) :
    -- (i)
    ((0 < k ∧ k < (1 - K a) / (1 + K a)) →
      ∀ ε > (0 : ℝ), ∃ β > (0 : ℝ), ∀ ω ∈ delaySpectrum a k ε, ω.re ≤ -β) ∧
    -- (ii), with the standing `k > 0` of p. 152 made explicit
    ((k = (1 - K a) / (1 + K a) ∧ 0 < k) →
      (∀ ε > (0 : ℝ), ∀ ω ∈ delaySpectrum a k ε, ω.re < 0) ∧
        ∃ R : Set ℝ, IsCountablyDenseInPos R ∧ ∀ ε ∈ R, ∃ ω : ℕ → ℂ,
          (∀ j, ω j ∈ delaySpectrum a k ε) ∧
            Filter.Tendsto (fun j => (ω j).re) Filter.atTop (nhds 0)) ∧
    -- (iii)
    ((1 - K a) / (1 + K a) < k →
      ∃ D : Set ℝ, IsOpenDenseInPos D ∧
        ∀ ε ∈ D, ∃ u : ℝ → ℝ → ℂ, IsExpUnstableSolution a k ε u) := by sorry

end DatkoDelayWave.BoundaryDelay
