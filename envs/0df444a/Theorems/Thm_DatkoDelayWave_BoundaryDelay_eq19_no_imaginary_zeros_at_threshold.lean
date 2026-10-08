-- Prove2me | Theorems.Thm_DatkoDelayWave_BoundaryDelay_eq19_no_imaginary_zeros_at_threshold
-- name    : DatkoDelayWave.BoundaryDelay.eq19_no_imaginary_zeros_at_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:59:20.967975+00:00
-- url     : https://prove2.me/theorems/7c6f378e-278c-48f7-bf92-01d09d4ed7bf
-- title:
--   Eq. (19) — at the critical gain k = (1−K)/(1+K), a > 0, h has no zero iη with η ≠ 0
-- statement:
--   Let $a > 0$, $K = e^{-2a}$, $k = (1-K)/(1+K)$ and $\varepsilon > 0$. Then for every real $\eta \neq 0$,
--   $$
--   h(\varepsilon, i\eta) \neq 0 .
--   $$
--
--   The paper derives this from (19), $1 + a/(i\eta) = k e^{-i\varepsilon\eta}(Ke^{-2i\eta} - 1)/(Ke^{-2i\eta} + 1)$, by comparing moduli. With Eqs. (17)–(18) it places the spectrum at the critical gain in the open left half-plane.
--
--   **Formalization Note** The hypothesis $a > 0$ is the paper's standing "$k > 0$" (p. 152) at the critical gain; at $a = 0$ the critical gain is $k = 0$ and $h(\varepsilon,\omega) = \omega(1 + e^{-2\omega})$ vanishes at $\omega = (n + \tfrac12)\pi i$.
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), p. 155, proof of the Theorem, part (ii), Eq. (19) and the display after it

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

namespace DatkoDelayWave.BoundaryDelay

theorem eq19_no_imaginary_zeros_at_threshold (a k ε : ℝ) (ha : 0 < a)
    (hkK : k = (1 - K a) / (1 + K a)) (hε : 0 < ε) (η : ℝ) (hη : η ≠ 0) :
    h a k ε ((η : ℂ) * Complex.I) ≠ 0 := by sorry

end DatkoDelayWave.BoundaryDelay
