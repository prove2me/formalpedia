-- Prove2me | Theorems.Thm_DelayedGLCB_proposition_1_1
-- name    : DelayedGLCB.proposition_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:25:14.63355+00:00
-- url     : https://prove2.me/theorems/ca64ccf0-0d24-4e05-b130-b99ea3b82592
-- title:
--   Proposition 1-1 — $G_t$ is sub-Gaussian and satisfies the tail bound (6) (corrected: envelope $\xi$ on $[0,\infty)$)
-- statement:
--   Let $D_1,\dots,D_T$ be independent non-negative delays with tail envelope $(\xi,\mu,M)$, where $M>0$, $q\ge0$, $\sigma>0$ (Assumption 2), and write $\sigma_G=\sigma\sqrt{2+q}$, $C_3=2\sigma^2+1$. Let $G_t$ be the number of missing rewards at round $t$. Then for every $t\in[1,T]$:
--
--   1. $G_t-\mathbb E[G_t]$ has a sub-Gaussian moment generating function for some variance proxy;
--   2. for every $\delta>0$,
--   $$
--   P\Big(G_t>2(\mu+M)+\sigma_G\sqrt{2\log\tfrac1\delta}+2\sigma_G^2\log C_3+1\Big)\le\delta.
--   $$
--
--   The number of missing rewards thus stays within $2(\mu+M)$ plus a sub-Gaussian fluctuation, uniformly in $t$, even though the delays are unbounded. This drives the width $\beta_t$ of DUCB-GLCB and the regret bound.
--
--   Differences from the source:
--   - correction: ξ a distribution with mean µ < ∞ → ξ a probability measure on [0, ∞) with finite mean µ; reason: over all of ℝ the statement is false: ξ = point mass at −100 (µ = −100), M = 10, σ = 0.1, q = 0, D_t ≡ 9.5 satisfy every clause of Assumption 2, yet G_t ≥ 9 for t ≥ 10 while the right side of (6) is negative; ξ is introduced as an envelope delay distribution (p.6) and the proof uses E[D_t] ≤ µ + M (p.23)
--   - reading: G_t = Σ_{s=1}^{t−1} 𝕀{s + D_s ≥ t} and T_t = {s ≤ t − 1 : s + D_s ≤ t − 1} → G_t = #{s ∈ [1, t − 1] : s + D_s > t − 1} = (t − 1) − |T_t|; reason: Algorithm 1 (lines 2, 7) sets G_t = (t − 1) − |T_t|; for a fractional delay the printed sum and this count disagree, and the reward of round s is read as arriving at the end of round ⌈s + D_s⌉; for integer delays the two coincide
--   - reading: P(D − µ ≥ x) ≤ exp(−x^{1+q}/(2σ²)) → the inequality for every x ≥ 0, with x^{1+q} the real power; reason: x^{1+q} is not defined for negative x when q is not an integer, and for x < 0 the bound is not meant
--   - encoding: for all t ≥ 1 (Assumption 2 on t ∈ [T]) → for every horizon T and every t ∈ [1, T]; reason: T is arbitrary, so every t ≥ 1 is covered
--   - reading: G_t is sub-Gaussian → ∃ c, G_t − E[G_t] has a sub-Gaussian MGF with parameter c; reason: the clause names no parameter
--   - encoding: random variables D_t (and features) → measurable functions, non-negativity and the unit-ball bound at every outcome; reason: standing convention of probability; no instance of the paper is excluded up to null-set modification
--   - encoding: with probability (at least) 1 − δ, the bound holds → P(the bound fails) ≤ δ; reason: complement form; for measurable events the two are the same
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, Proposition 1, part 1, (6), p.8

import Mathlib
import Definitions.Def_DelayedGLCB_completeSet
import Definitions.Def_DelayedGLCB_TailEnvelope

namespace DelayedGLCB

open MeasureTheory ProbabilityTheory

/-- **Proposition 1-1 (`G_t` is sub-Gaussian, and the tail bound (6)).**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, Proposition 1, part 1, (6), p.8: "Assume Assumption 2.
Denote `σ_G = σ√(2+q)`. Then, 1. `G_t` is sub-Gaussian. Moreover, for all `t ≥ 1`, with probability
`1 − δ`, `G_t ≤ 2(µ + M) + σ_G √(2 log(1/δ)) + 2σ_G² log C₃ + 1`, (6) where `C₃ = 2σ² + 1`."

For independent non-negative delays `D_1, …, D_T` with tail envelope `(ξ, µ, M)` (Assumption 2):
for every `t ∈ [1, T]`, `G_t − E[G_t]` has a sub-Gaussian moment generating function for some
parameter, and for every `δ > 0`,
`P(G_t > 2(µ+M) + σ_G √(2 log(1/δ)) + 2σ_G² log C₃ + 1) ≤ δ`.
The radical covers `2 log(1/δ)` only (rendered p.8, and the proof's last display on p.24).

**Formalization Note.** `G_t = missingCount D ω t` (rounds `s < t` with `s + D_s > t − 1`). "For all
`t ≥ 1`" is `t ∈ [1, T]` for the horizon `T` of Assumption 2. The sub-Gaussian clause has no stated
parameter, so it is existential. -/
theorem proposition_1_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (T : ℕ) (ξ : Measure ℝ) (μ M q σ : ℝ) (hM : 0 < M) (hq : 0 ≤ q) (hσ : 0 < σ)
    (hD : IndepDelays P D T) (hξ : TailEnvelope P D T ξ μ M q σ) :
    ∀ t ∈ Finset.Icc 1 T,
      (∃ c : NNReal, HasSubgaussianMGF
        (fun ω => (missingCount D ω t : ℝ) - ∫ ω', (missingCount D ω' t : ℝ) ∂P) c P) ∧
      ∀ δ : ℝ, 0 < δ →
        P {ω | 2 * (μ + M) + sigmaG σ q *
            Real.sqrt (2 * Real.log (1 / δ)) + 2 * sigmaG σ q ^ 2 * Real.log (C3 σ) + 1
              < (missingCount D ω t : ℝ)} ≤ ENNReal.ofReal δ := by sorry

end DelayedGLCB
