-- Prove2me | Theorems.Thm_DatkoDelayWave_BoundaryDelay_eq12_15_root_above_threshold
-- name    : DatkoDelayWave.BoundaryDelay.eq12_15_root_above_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:59:36.215484+00:00
-- url     : https://prove2.me/theorems/25d693ac-298b-43f5-8fef-c6a38f03ae63
-- title:
--   Eqs. (12)–(15) — above the critical gain, f(2(2m+1)/(2n+1), ω₁ + (2n+1)πi/2) = 0 for some ω₁ > 0
-- statement:
--   Let $a \ge 0$, $K = e^{-2a}$ and $k > (1-K)/(1+K)$. Then for all integers $m, n \ge 1$ there is a real $\omega_1 > 0$ with
--   $$
--   f\!\left(\frac{2(2m+1)}{2n+1},\ \omega_1 + \frac{(2n+1)\pi i}{2}\right) = 0 .
--   $$
--
--   In the paper, $\omega_1$ is a solution of (14), and (12)–(15) show that $\omega = \omega_1 + \tfrac{2n+1}{2}\pi i$ solves the characteristic relation for the delay $\varepsilon = 2(2m+1)/(2n+1)$. This is the zero in the open right half-plane from which Lemma 2 is built.
--
--   **Formalization Note** The page writes the relation through the logarithms of (11), (13), (14); the statement here is the logarithm-free identity $f = 0$ they encode, which avoids the page's claim that the principal branch is used (the argument of the logarithm is a negative real at these points). As on the page, $m$ and $n$ are positive integers.
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), p. 154, proof of Lemma 2, Eqs. (12)–(15) and the paragraph after (15)

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

namespace DatkoDelayWave.BoundaryDelay

theorem eq12_15_root_above_threshold (a k : ℝ) (ha : 0 ≤ a)
    (hkK : (1 - K a) / (1 + K a) < k) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ ω₁ : ℝ, 0 < ω₁ ∧
      f a k (2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1))
        ((ω₁ : ℂ) + (2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2) = 0 := by sorry

end DatkoDelayWave.BoundaryDelay
