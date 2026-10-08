-- Prove2me | Theorems.Thm_DatkoDelayWave_BoundaryDelay_undelayed_real_part
-- name    : DatkoDelayWave.BoundaryDelay.undelayed_real_part
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:00:57.278646+00:00
-- url     : https://prove2.me/theorems/5ebf21ab-6dd4-4b79-9a4f-90f79fa95d50
-- title:
--   Undelayed case a = 0, k ≠ 1 — every eigenvalue has Re ω = ½ log|(k−1)/(k+1)| < 0
-- statement:
--   Consider the undelayed problem (5), (6) with $a = 0$: $\varphi'' = \omega^2\varphi$ on $(0,1)$, $\varphi(0) = 0$, $\varphi'(1) + k\omega\varphi(1) = 0$. Let $k > 0$, $k \neq 1$. Then every eigenvalue $\omega$ satisfies
--   $$
--   \operatorname{Re}\omega = \tfrac12 \log\left|\frac{k-1}{k+1}\right| < 0 .
--   $$
--
--   This is the explicit decay rate of the boundary-damped string without delay, the baseline against which the delayed system is compared.
--
--   **Formalization Note** The undelayed spectrum is the spectrum $\sigma(0,k,0)$ of the model's definition with zero delay. The printed "$< 0$" needs $k > 0$ (at $k = 0$ the real part is $0$); the hypothesis $k > 0$ is the paper's standing "$k > 0$" of p. 152.
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), p. 153, display after Eq. (7)

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

namespace DatkoDelayWave.BoundaryDelay

theorem undelayed_real_part (k : ℝ) (hk : 0 < k) (hk1 : k ≠ 1) :
    ∀ ω ∈ delaySpectrum 0 k 0,
      ω.re = (1 / 2) * Real.log |(k - 1) / (k + 1)| ∧ ω.re < 0 := by sorry

end DatkoDelayWave.BoundaryDelay
