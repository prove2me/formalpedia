-- Prove2me | Theorems.Thm_DatkoDelayWave_BoundaryDelay_no_accumulation_imaginary_axis
-- name    : DatkoDelayWave.BoundaryDelay.no_accumulation_imaginary_axis
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:59:18.653931+00:00
-- url     : https://prove2.me/theorems/946a4191-47b7-43ac-a45c-de3a2f6f6f13
-- title:
--   Proof of Theorem (i) — below the critical gain the zeros of h stay in a half-plane Re ω ≤ −β
-- statement:
--   Let $a \ge 0$, $K = e^{-2a}$, $0 < k < (1-K)/(1+K)$ and $\varepsilon > 0$. Then the zeros of $h(\varepsilon,\cdot)$ do not accumulate at the imaginary axis: there is $\beta > 0$ such that
--   $$
--   h(\varepsilon,\omega) = 0 \implies \operatorname{Re}\omega \le -\beta .
--   $$
--
--   The paper shows that no sequence of zeros $\omega_n = \xi_n + i\eta_n$ can have $\xi_n \to 0$; together with Eqs. (17)–(18) this is the half-plane bound of Theorem (i).
--
--   **Formalization Note** The page's assertion "it is not possible for a sequence of such zeros to accumulate at the imaginary axis" is formalized in its equivalent half-plane form, which is the conclusion the page draws from it. $\beta$ may depend on $\varepsilon$, $a$ and $k$. At $a = 0$ the hypothesis is empty.
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), p. 155, proof of the Theorem, part (i), display after (18)

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

namespace DatkoDelayWave.BoundaryDelay

theorem no_accumulation_imaginary_axis (a k ε : ℝ) (ha : 0 ≤ a) (hk : 0 < k)
    (hkK : k < (1 - K a) / (1 + K a)) (hε : 0 < ε) :
    ∃ β > (0 : ℝ), ∀ ω : ℂ, h a k ε ω = 0 → ω.re ≤ -β := by sorry

end DatkoDelayWave.BoundaryDelay
