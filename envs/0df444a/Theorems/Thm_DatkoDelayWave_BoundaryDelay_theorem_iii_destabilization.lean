-- Prove2me | Theorems.Thm_DatkoDelayWave_BoundaryDelay_theorem_iii_destabilization
-- name    : DatkoDelayWave.BoundaryDelay.theorem_iii_destabilization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:00:23.589786+00:00
-- url     : https://prove2.me/theorems/bb58fcb2-3d97-43dc-b287-04ba448241b4
-- title:
--   Theorem (iii) — for k > (1−K)/(1+K) an open dense set of delays admits exponentially unstable solutions
-- statement:
--   Let $a \ge 0$, $K = e^{-2a}$ and $k > (1-K)/(1+K)$. Then there is an open set $D \subseteq (0,\infty)$, dense in $(0,\infty)$, such that for every $\varepsilon \in D$ the delayed system (1), (2), (8) admits an exponentially unstable classical solution: a $C^2$ solution $u$ together with $\gamma > 0$, $c > 0$ and $x_0 \in (0,1)$ such that
--   $$
--   |u(x_0,t)| \ge c\,e^{\gamma t}\qquad (t \ge 0).
--   $$
--
--   Above the critical gain, arbitrarily small delays (from a dense set) destroy the stability of a system that is uniformly exponentially stable without delay.
--
--   **Formalization Note** The paper does not define "exponentially unstable solution"; it is read as a genuine complex-valued classical solution with pointwise exponential growth at some interior point. The real part of such a solution is a real solution.
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), p. 153, THEOREM (iii) (proof p. 155)

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

namespace DatkoDelayWave.BoundaryDelay

theorem theorem_iii_destabilization (a k : ℝ) (ha : 0 ≤ a)
    (hkK : (1 - K a) / (1 + K a) < k) :
    ∃ D : Set ℝ, IsOpenDenseInPos D ∧
      ∀ ε ∈ D, ∃ u : ℝ → ℝ → ℂ, IsExpUnstableSolution a k ε u := by sorry

end DatkoDelayWave.BoundaryDelay
