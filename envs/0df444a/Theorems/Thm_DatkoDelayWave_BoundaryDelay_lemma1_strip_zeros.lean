-- Prove2me | Theorems.Thm_DatkoDelayWave_BoundaryDelay_lemma1_strip_zeros
-- name    : DatkoDelayWave.BoundaryDelay.lemma1_strip_zeros
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:58:51.119769+00:00
-- url     : https://prove2.me/theorems/3fbd9561-1e58-4c4d-ac49-765e3a2dfa1f
-- title:
--   Lemma 1 — a zero of f(ε, ·) gives infinitely many zeros of f and of h in every vertical strip around it
-- statement:
--   Let $a \ge 0$, $k \ge 0$, $\varepsilon > 0$, $K = e^{-2a}$, and
--   $$
--   f(\varepsilon,\omega) = 1 + K e^{-2\omega} + k e^{-\varepsilon\omega}(1 - K e^{-2\omega}),\qquad h(\varepsilon,\omega) = \omega f(\varepsilon,\omega) + a(1 + K e^{-2\omega}).
--   $$
--   If $f(\varepsilon,\omega_0) = 0$ for some $\omega_0 = \xi_0 + i\eta_0$, then for every $\delta > 0$ the open vertical strip $\{\omega : \xi_0 - \delta < \operatorname{Re}\omega < \xi_0 + \delta\}$ contains infinitely many zeros of $f(\varepsilon,\cdot)$ and infinitely many zeros of $h(\varepsilon,\cdot)$.
--
--   The paper quotes this as a special case of Datko (1978), Lemma 2.3, and uses it to pass from a single zero of $f$ to infinitely many spectral points.
--
--   **Formalization Note** "An infinite number of zeros" is read as: the set of zeros in the strip is infinite, separately for $f$ and for $h$ (no multiplicities).
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), p. 153, Lemma 1 (with Eq. (9))

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

namespace DatkoDelayWave.BoundaryDelay

theorem lemma1_strip_zeros (a k ε : ℝ) (ha : 0 ≤ a) (hk : 0 ≤ k) (hε : 0 < ε)
    (ω₀ : ℂ) (hf : f a k ε ω₀ = 0) (δ : ℝ) (hδ : 0 < δ) :
    {ω : ℂ | ω₀.re - δ < ω.re ∧ ω.re < ω₀.re + δ ∧ f a k ε ω = 0}.Infinite ∧
      {ω : ℂ | ω₀.re - δ < ω.re ∧ ω.re < ω₀.re + δ ∧ h a k ε ω = 0}.Infinite := by sorry

end DatkoDelayWave.BoundaryDelay
