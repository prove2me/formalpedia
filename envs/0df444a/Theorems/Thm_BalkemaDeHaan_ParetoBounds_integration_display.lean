-- Prove2me | Theorems.Thm_BalkemaDeHaan_ParetoBounds_integration_display
-- name    : BalkemaDeHaan.ParetoBounds.integration_display
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:48:30.1493+00:00
-- url     : https://prove2.me/theorems/de3070db-7bed-466b-b543-e8959e7c92da
-- title:
--   Proof of Theorem 6, p. 801 — integrating $\alpha_1 \le uF'(u)/(1 - F(u)) \le \alpha_2$ over $[t, (1+x)t]$
-- statement:
--   Let $F$ be a distribution function on $\mathbb R$ which has a positive density $F'$ for $u \ge t_0$, and let $\alpha_1, \alpha_2 > 0$ satisfy
--
--   $$
--   \alpha_1 \le \frac{u F'(u)}{1 - F(u)} \le \alpha_2 \qquad \text{for } u \ge t_0 .
--   $$
--
--   Then for every $t \ge t_0$ and every $x > 0$,
--
--   $$
--   \alpha_1 \int_t^{(1+x)t} \frac{du}{u} \;\le\; \int_t^{(1+x)t} \frac{F'(u)}{1 - F(u)}\,du \;\le\; \alpha_2 \int_t^{(1+x)t} \frac{du}{u} .
--   $$
--
--   This is the integrated form of the hazard-rate bounds: the middle integral is the increase of the cumulative hazard $-\log(1 - F)$ between $t$ and $(1+x)t$, and the outer integrals equal $\alpha_i \log(1+x)$. Applying the monotone map $y \mapsto 1 - e^{-y}$ turns it into Theorem 6.
--
--   **Formalization Note** $F$ is `cdf μ` for a probability measure $\mu$, and the density is an explicit function $f$ with $F$ differentiable at every $u \ge t_0$ with derivative $f(u) > 0$, the derivative being taken within $[t_0, \infty)$ (so only a right derivative is required at $t_0$ itself; for $u > t_0$ this is the ordinary derivative). The integrals are oriented interval integrals; the hypotheses force $t_0 > 0$ (at $u \le 0$ the ratio is $\le 0 < \alpha_1$), so $t < (1+x)t$. The integrand $F'(u)/(1-F(u))$ is not assumed integrable: under the hypotheses it is bounded on $[t, (1+x)t]$ and measurable there, so the statement does not rest on Lean's value $0$ for non-integrable functions (that value would make the first inequality false, not trivially true).
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 801 (PDF p. 10), §4, proof of Theorem 6, display

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.ParetoBounds

/-- Proof of Theorem 6, p. 801 (Balkema–de Haan 1974): integrating the hazard bounds
`α₁ ≤ t F'(t)/(1 - F(t)) ≤ α₂` between `t` and `(1 + x) t`, `x > 0`, gives
`α₁ ∫ du/u ≤ ∫ F'(u)/(1 - F(u)) du ≤ α₂ ∫ du/u`. The density `F' = f` is a (right,
at `t₀`) derivative of `F = cdf μ` on `[t₀, ∞)`. -/
theorem integration_display (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (t₀ α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hdens : ∀ t ≥ t₀, HasDerivWithinAt (cdf μ) (f t) (Set.Ici t₀) t ∧ 0 < f t)
    (hbounds : ∀ t ≥ t₀, α₁ ≤ t * f t / (1 - cdf μ t) ∧ t * f t / (1 - cdf μ t) ≤ α₂)
    (t : ℝ) (ht : t₀ ≤ t) (x : ℝ) (hx : 0 < x) :
    α₁ * ∫ u in t..(1 + x) * t, 1 / u ≤ ∫ u in t..(1 + x) * t, f u / (1 - cdf μ u) ∧
      ∫ u in t..(1 + x) * t, f u / (1 - cdf μ u) ≤ α₂ * ∫ u in t..(1 + x) * t, 1 / u := by sorry

end BalkemaDeHaan.ParetoBounds
