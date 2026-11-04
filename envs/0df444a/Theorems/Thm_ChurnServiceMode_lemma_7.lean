-- Prove2me | Theorems.Thm_ChurnServiceMode_lemma_7
-- name    : ChurnServiceMode.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:44.673919+00:00
-- url     : https://prove2.me/theorems/4bc69588-01a6-4c31-a8ef-fbf749428890
-- title:
--   Lemma 7 — reflected O-U dominates the unreflected O-U in the stochastic order
-- statement:
--   Let $B$ be a standard Brownian motion, $\sigma_0>0$, $\theta_0\in\mathbb R$. Let $X$ be a $(\sigma_0,\theta_0)$ reflected O-U process driven by $B$ started at $x>0$ (Definition 3), and let $Y$ be the unreflected process started at $y\le x$:
--   $$Y_t=y+\theta_0t-\int_0^tY_s\,ds+\sigma_0B_t\qquad\text{(display (23))}.$$
--   Then for every $t\ge0$, $X_t\ge_{\rm st}Y_t$ and $X_t\ge_{\rm st}Y_t^+$, where $Y_t^+=\max(Y_t,0)$ and $\ge_{\rm st}$ is the usual stochastic order: $P(Y_t>c)\le P(X_t>c)$ for every real $c$ (and likewise for $Y_t^+$).
--
--   The lemma is the comparison used in the proof of Proposition 1 to bound passage times of the satisfaction process inside a Risky interval.
--
--   **Formalization Note** $B$ is a standard Brownian motion with respect to some filtration; Definition 3 and (23) hold for almost every path. Probabilities of possibly non-measurable events are outer measures.
--
--   Differences from the source:
--   - encoding: processes X, Y, L satisfying Definition 3 and (23) → almost every path satisfies IsReflectedOUPath and (23); ≥st as P{Y_t > c} ≤ P{X_t > c} for all c; reason: pathwise reading of process identities; the usual stochastic order on ℝ
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Lemma 7 with display (23) and Definition 3, p.23 (PDF p.23)

import Mathlib
import Definitions.Def_ChurnServiceMode_IsReflectedOUPath
import Definitions.Def_PeskirShiryaev_LocalTime_Diffusion

open MeasureTheory ProbabilityTheory Filter PeskirShiryaev.LocalTime
open scoped NNReal ENNReal Topology

namespace ChurnServiceMode

/-- **Lemma 7** (Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode Control*, SSRN 3188226 (Dec 1, 2022), p.23). Let `B` be a standard Brownian motion, `X` a `(σ₀, θ₀)` reflected
O-U process (Definition 3) driven by `B` and started at `x > 0`, and `Y` the unreflected process
`Y_t = y + θ₀ t − ∫₀ᵗ Y_s ds + σ₀ B_t` (display (23)) started at `y ≤ x`. Then `X_t ≥st Y_t` and
`X_t ≥st Y_t⁺ = max(Y_t, 0)` for every `t ≥ 0`, where `≥st` is the usual stochastic order:
`P(Y_t > c) ≤ P(X_t > c)` for every real `c`.

**Formalization Note.** `B` is a standard Brownian motion for some filtration (the published
`FilteredBrownian`); Definition 3 and (23) are required of almost every path. The probabilities are
outer measures, so no measurability of `X` or `Y` is assumed. -/
theorem lemma_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (B : ℝ≥0 → Ω → ℝ) (hB : FilteredBrownian P ℱ B)
    (σ₀ θ₀ x y : ℝ) (hx : 0 < x) (hyx : y ≤ x) (X L Y : ℝ≥0 → Ω → ℝ)
    (hX : ∀ᵐ ω ∂P, IsReflectedOUPath σ₀ θ₀ x (fun t => B t ω) (fun t => X t ω) (fun t => L t ω))
    (hY : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Y t ω = y + θ₀ * t - (∫ s in (0 : ℝ)..(t : ℝ), Y s.toNNReal ω) + σ₀ * B t ω) :
    ∀ (t : ℝ≥0) (c : ℝ),
      P {ω | c < Y t ω} ≤ P {ω | c < X t ω} ∧
      P {ω | c < max (Y t ω) 0} ≤ P {ω | c < X t ω} := by sorry

end ChurnServiceMode
