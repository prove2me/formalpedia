-- Prove2me | Theorems.Thm_DatkoDelayWave_BoundaryDelay_threshold_explicit_zero
-- name    : DatkoDelayWave.BoundaryDelay.threshold_explicit_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:59:50.67228+00:00
-- url     : https://prove2.me/theorems/fd49332a-fb12-41be-9f07-7402737927d2
-- title:
--   Proof of Theorem (ii) — at the critical gain, f(2(2m+1)/(2n+1), (2n+1)πi/2) = 0
-- statement:
--   Let $a \ge 0$, $K = e^{-2a}$ and $k = (1-K)/(1+K)$. Then for all integers $m, n \ge 0$,
--   $$
--   f\!\left(\frac{2(2m+1)}{2n+1},\ \frac{(2n+1)\pi i}{2}\right) = 0,
--   $$
--   where $f(\varepsilon,\omega) = 1 + Ke^{-2\omega} + ke^{-\varepsilon\omega}(1 - Ke^{-2\omega})$.
--
--   Combined with Lemma 1, this zero on the imaginary axis forces infinitely many spectral points in every strip $-\delta < \operatorname{Re}\omega < 0$ for these delays.
--
--   **Formalization Note** The page says "$m, n$ are arbitrary"; the identity is stated for all natural numbers $m, n$ (including $0$).
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), p. 155, proof of the Theorem, part (ii), display after (19)

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

namespace DatkoDelayWave.BoundaryDelay

theorem threshold_explicit_zero (a k : ℝ) (ha : 0 ≤ a)
    (hkK : k = (1 - K a) / (1 + K a)) (m n : ℕ) :
    f a k (2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1))
      ((2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2) = 0 := by sorry

end DatkoDelayWave.BoundaryDelay
