-- Prove2me | Theorems.Thm_DatkoDelayWave_BoundaryDelay_eq17_18_no_right_half_plane_zeros
-- name    : DatkoDelayWave.BoundaryDelay.eq17_18_no_right_half_plane_zeros
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:59:11.531368+00:00
-- url     : https://prove2.me/theorems/b3875b24-9b49-463c-8896-67090666718b
-- title:
--   Eqs. (17)–(18) — for k ≤ (1−K)/(1+K) no zero of h has Re ω > 0, and for k < (1−K)/(1+K) none has Re ω ≥ 0
-- statement:
--   Let $a \ge 0$, $k \ge 0$, $\varepsilon > 0$ and $K = e^{-2a}$, and let $h$ be the function of (9).
--
--   1. If $k \le (1-K)/(1+K)$, every zero $\omega$ of $h(\varepsilon,\cdot)$ satisfies $\operatorname{Re}\omega \le 0$.
--   2. If $k < (1-K)/(1+K)$, every zero $\omega$ of $h(\varepsilon,\cdot)$ satisfies $\operatorname{Re}\omega < 0$.
--
--   In formulas,
--   $$
--   k \le \tfrac{1-K}{1+K} \implies \bigl(h(\varepsilon,\omega) = 0 \Rightarrow \operatorname{Re}\omega \le 0\bigr),\qquad
--   k < \tfrac{1-K}{1+K} \implies \bigl(h(\varepsilon,\omega) = 0 \Rightarrow \operatorname{Re}\omega < 0\bigr).
--   $$
--
--   This is the first step of the proof of parts (i) and (ii) of the THEOREM.
--
--   **Formalization Note** The page assumes $a > 0$ implicitly ("$\omega = 0$ is not a solution of (16)"). The statement is kept for $a \ge 0$: at $a = 0$ the hypothesis forces $k = 0$ in item 1, where the zeros of $h = \omega(1 + e^{-2\omega})$ lie on the imaginary axis, and item 2 is vacuous.
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), pp. 154–155, proof of the Theorem, part (i), Eqs. (17), (18) and the sentence after (18)

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

namespace DatkoDelayWave.BoundaryDelay

theorem eq17_18_no_right_half_plane_zeros (a k ε : ℝ) (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hε : 0 < ε) :
    (k ≤ (1 - K a) / (1 + K a) → ∀ ω : ℂ, h a k ε ω = 0 → ω.re ≤ 0) ∧
      (k < (1 - K a) / (1 + K a) → ∀ ω : ℂ, h a k ε ω = 0 → ω.re < 0) := by sorry

end DatkoDelayWave.BoundaryDelay
