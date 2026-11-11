-- Prove2me | Theorems.Thm_ContinualHardness_Linear_eq_6
-- name    : ContinualHardness.Linear.eq_6
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T14:11:14.132681+00:00
-- url     : https://prove2.me/theorems/cb06933b-5f06-4481-81fb-5dcbb9f4c5bc
-- title:
--   §A.1, Eq. (6) — Gaussian anti-concentration: Pr[g ∈ [t, t + δ]] ≤ δ/(σ√(2π)) for g ∼ N(0, σ²)
-- statement:
--   Let $\sigma>0$ and let $g\sim N(0,\sigma^2)$ be a centred Gaussian with variance $\sigma^2$. For every $t\in\mathbb R$ and every $\delta\ge0$,
--   $$\Pr\big[g\in[t,t+\delta]\big]\ \le\ \frac{\delta}{\sigma\sqrt{2\pi}} .$$
--   The bound follows from the maximum $1/(\sigma\sqrt{2\pi})$ of the Gaussian density; in the soundness proof of the dictatorship test (Lemma A.7) it bounds the probability that a Gaussian approximation of $r_t^{\mathsf T}x_t$ falls in a short interval.
--
--   **Formalization Note.** $N(0,\sigma^2)$ is Mathlib's `gaussianReal 0 (σ²)` and the probability is the measure of the closed interval $[t,t+\delta]$.
--
--   Differences from the source:
--   - reading: δ, t and σ unquantified ('for g ∼ N(0, σ²)') → every σ > 0, t ∈ ℝ and δ ≥ 0; reason: the interval [t, t + δ] needs δ ≥ 0 (for δ < 0 the right side is negative), and N(0, σ²) with σ > 0 is the non-degenerate Gaussian the bound is about
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), p. 16, §A.1, Eq. (6) (PDF p. 17)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ContinualHardness.Linear

/-- §A.1, Eq. (6), p. 16 (Gaussian anti-concentration). For `g ∼ N(0, σ²)` with `σ > 0`, every
`t ∈ ℝ` and every `δ ≥ 0`: `Pr[g ∈ [t, t + δ]] ≤ δ/(σ√(2π))`. -/
theorem eq_6 (σ t δ : ℝ) (hσ : 0 < σ) (hδ : 0 ≤ δ) :
    (gaussianReal 0 (σ ^ 2).toNNReal (Set.Icc t (t + δ))).toReal
      ≤ δ / (σ * Real.sqrt (2 * Real.pi)) := by sorry

end ContinualHardness.Linear
