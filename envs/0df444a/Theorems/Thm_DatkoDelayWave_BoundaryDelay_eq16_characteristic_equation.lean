-- Prove2me | Theorems.Thm_DatkoDelayWave_BoundaryDelay_eq16_characteristic_equation
-- name    : DatkoDelayWave.BoundaryDelay.eq16_characteristic_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:58:48.317696+00:00
-- url     : https://prove2.me/theorems/c620772b-2eae-434a-af53-971ea3652a2e
-- title:
--   Eq. (16) — away from ω = −a, ω is in the spectrum iff h(ε, ω) = 0
-- statement:
--   Let $a \ge 0$, $k \ge 0$, $\varepsilon > 0$, and let $\sigma(a,k,\varepsilon)$ be the spectrum of the delayed system (1), (2), (8), defined through the eigenvalue problem $\varphi'' = (a+\omega)^2\varphi$ on $(0,1)$, $\varphi(0) = 0$, $\varphi'(1) + k\omega e^{-\varepsilon\omega}\varphi(1) = 0$. Then for every $\omega \in \mathbb C$ with $\omega \neq -a$,
--   $$
--   \omega \in \sigma(a,k,\varepsilon) \iff h(\varepsilon,\omega) = 0,
--   $$
--   where $h(\varepsilon,\omega) = \omega\bigl[1 + K e^{-2\omega} + k e^{-\varepsilon\omega}(1 - K e^{-2\omega})\bigr] + a(1 + K e^{-2\omega})$ and $K = e^{-2a}$.
--
--   This is the characteristic equation through which every spectral statement of the paper is proved.
--
--   **Formalization Note** The page states the equivalence without exception. The value $\omega = -a$ is excluded because there the eigenfunction is $\varphi(x) = cx$ rather than $\sinh((a+\omega)x)$: $h(\varepsilon,-a) = 0$ for every $\varepsilon$, while $-a \in \sigma$ only if $1 = kae^{\varepsilon a}$. Since $-a \le 0$, this exception does not affect the THEOREM.
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), p. 154, proof of the Theorem, Eq. (16)

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

namespace DatkoDelayWave.BoundaryDelay

theorem eq16_characteristic_equation (a k ε : ℝ) (ha : 0 ≤ a) (hk : 0 ≤ k) (hε : 0 < ε)
    (ω : ℂ) (hω : ω ≠ -(a : ℂ)) :
    ω ∈ delaySpectrum a k ε ↔ h a k ε ω = 0 := by sorry

end DatkoDelayWave.BoundaryDelay
