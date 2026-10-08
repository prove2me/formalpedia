-- Prove2me | Theorems.Thm_DatkoDelayWave_BoundaryDelay_theorem_ii_threshold
-- name    : DatkoDelayWave.BoundaryDelay.theorem_ii_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:00:12.004361+00:00
-- url     : https://prove2.me/theorems/8101ba50-9e81-4093-ba84-f9b9fd53491d
-- title:
--   Theorem (ii) — at k = (1−K)/(1+K) > 0 the spectrum is in Re ω < 0 but approaches the axis for a countable dense set of delays
-- statement:
--   Let $a \ge 0$, $K = e^{-2a}$ and $k = (1-K)/(1+K)$ with $k > 0$. Then
--
--   1. for each $\varepsilon > 0$, every $\omega \in \sigma(a,k,\varepsilon)$ satisfies $\operatorname{Re}\omega < 0$;
--   2. there is a countable set $R \subseteq (0,\infty)$, dense in $(0,\infty)$, such that for each $\varepsilon \in R$ there is a sequence $(\omega_n)$ in $\sigma(a,k,\varepsilon)$ with
--   $$
--   \lim_{n\to\infty} \operatorname{Re}\omega_n = 0 .
--   $$
--
--   At the critical gain the system has no exponentially growing modes, but for a dense set of delays it loses its uniform spectral gap.
--
--   **Formalization Note** The hypothesis $k > 0$ (equivalently $a > 0$) is the paper's standing "$k > 0$" of p. 152; without it, at $a = 0$, the spectrum is $\{(n+\tfrac12)\pi i\}$ and item 1 fails. "Countably dense set $R$ in $(0,\infty)$" is read as countable, contained in $(0,\infty)$ and dense in $(0,\infty)$; the paper's proof gives $R = \{2(2m+1)/(2n+1)\}$.
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), p. 153, THEOREM (ii) (proof p. 155)

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

namespace DatkoDelayWave.BoundaryDelay

theorem theorem_ii_threshold (a k : ℝ) (ha : 0 ≤ a) (hk : 0 < k)
    (hkK : k = (1 - K a) / (1 + K a)) :
    (∀ ε > (0 : ℝ), ∀ ω ∈ delaySpectrum a k ε, ω.re < 0) ∧
      ∃ R : Set ℝ, IsCountablyDenseInPos R ∧ ∀ ε ∈ R, ∃ ω : ℕ → ℂ,
        (∀ j, ω j ∈ delaySpectrum a k ε) ∧
          Filter.Tendsto (fun j => (ω j).re) Filter.atTop (nhds 0) := by sorry

end DatkoDelayWave.BoundaryDelay
