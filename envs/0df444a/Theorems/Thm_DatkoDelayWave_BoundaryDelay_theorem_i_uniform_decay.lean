-- Prove2me | Theorems.Thm_DatkoDelayWave_BoundaryDelay_theorem_i_uniform_decay
-- name    : DatkoDelayWave.BoundaryDelay.theorem_i_uniform_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:00:36.227212+00:00
-- url     : https://prove2.me/theorems/675fde4f-17d5-4110-a402-7c0ca8b9d35d
-- title:
--   Theorem (i) — for 0 < k < (1−K)/(1+K) the spectrum lies in a half-plane Re ω ≤ −β(ε)
-- statement:
--   Let $a \ge 0$, $K = e^{-2a}$ and $0 < k < (1-K)/(1+K)$. Then for each delay $\varepsilon > 0$ there is $\beta = \beta(\varepsilon) > 0$ such that
--   $$
--   \operatorname{Re}\omega \le -\beta \quad\text{for every } \omega \in \sigma(a,k,\varepsilon),
--   $$
--   where $\sigma(a,k,\varepsilon)$ is the spectrum of the delayed system (1), (2), (8).
--
--   Below the critical gain, delays of any length preserve a uniform spectral gap.
--
--   **Formalization Note** $\beta$ depends on $\varepsilon$ (and on $a$, $k$), as in the paper. At $a = 0$ the hypothesis $0 < k < 0$ is empty, so the statement has content only for $a > 0$, as in the paper.
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), p. 153, THEOREM (i) (proof pp. 154–155)

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

namespace DatkoDelayWave.BoundaryDelay

theorem theorem_i_uniform_decay (a k : ℝ) (ha : 0 ≤ a) (hk : 0 < k)
    (hkK : k < (1 - K a) / (1 + K a)) :
    ∀ ε > (0 : ℝ), ∃ β > (0 : ℝ), ∀ ω ∈ delaySpectrum a k ε, ω.re ≤ -β := by sorry

end DatkoDelayWave.BoundaryDelay
