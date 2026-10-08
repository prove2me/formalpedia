-- Prove2me | Theorems.Thm_DatkoDelayWave_BoundaryDelay_lemma2_destabilizing_delays
-- name    : DatkoDelayWave.BoundaryDelay.lemma2_destabilizing_delays
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:59:45.425152+00:00
-- url     : https://prove2.me/theorems/b50c17f9-4aed-46fc-8bb6-f69d59db34b3
-- title:
--   Lemma 2 — above the critical gain, an open dense set of delays gives zeros of f in Re ω > 0
-- statement:
--   Let $a \ge 0$, $K = e^{-2a}$ and $k > (1-K)/(1+K)$. Then there is an open set $\mathcal D \subseteq (0,\infty)$, dense in $(0,\infty)$, such that for every $\varepsilon \in \mathcal D$ the equation
--   $$
--   f(\varepsilon,\omega) = 0
--   $$
--   has at least one solution $\omega$ with $\operatorname{Re}\omega > 0$.
--
--   With Lemma 1 this gives spectral points in the right half-plane, which is part (iii) of the THEOREM.
--
--   **Formalization Note** "An open dense set in $(0,\infty)$" is read as: $\mathcal D \subseteq (0,\infty)$ is open in $\mathbb R$ and every point of $(0,\infty)$ is in its closure. The delay $\varepsilon$ is real.
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), p. 153, Lemma 2 (proof pp. 153–154)

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

namespace DatkoDelayWave.BoundaryDelay

theorem lemma2_destabilizing_delays (a k : ℝ) (ha : 0 ≤ a)
    (hkK : (1 - K a) / (1 + K a) < k) :
    ∃ D : Set ℝ, IsOpenDenseInPos D ∧ ∀ ε ∈ D, ∃ ω : ℂ, 0 < ω.re ∧ f a k ε ω = 0 := by sorry

end DatkoDelayWave.BoundaryDelay
