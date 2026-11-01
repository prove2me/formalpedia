-- Prove2me | Theorems.Thm_DelayedGLCB_proposition_1_2
-- name    : DelayedGLCB.proposition_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:25:12.636706+00:00
-- url     : https://prove2.me/theorems/974b9cda-df13-464b-9658-4696bb758e5b
-- title:
--   Proposition 1-2 — the running maximum $G^*_T$ satisfies the tail bound (7) (corrected: envelope $\xi$ on $[0,\infty)$)
-- statement:
--   Let $D_1,\dots,D_T$ be independent non-negative delays with tail envelope $(\xi,\mu,M)$, where $M>0$, $q\ge0$, $\sigma>0$ (Assumption 2), $T\ge1$, and write $\sigma_G=\sigma\sqrt{2+q}$, $C_3=2\sigma^2+1$ and $G^*_T=\max_{1\le s\le T}G_s$. For every $\delta>0$,
--   $$
--   P\Big(G^*_T>2(\mu+M)+\sigma_G\sqrt{2\log T}+2\sigma_G^2\log C_3+\sigma_G\sqrt{2\log\tfrac1\delta+2\log C_3\,\sigma_G\sqrt{2\log T}+2\log C_3}+1\Big)\le\delta.
--   $$
--
--   The maximal number of missing rewards over $T$ rounds is $2(\mu+M)+O(\sigma_G\sqrt{\log T})$ with high probability. This is the delay term in the regret bound (16).
--
--   Differences from the source:
--   - correction: ξ a distribution with mean µ < ∞ → ξ a probability measure on [0, ∞) with finite mean µ; reason: over all of ℝ the statement is false: ξ = point mass at −100 (µ = −100), M = 10, σ = 0.1, q = 0, D_t ≡ 9.5 satisfy every clause of Assumption 2, yet G_t ≥ 9 for t ≥ 10 while the right side of (6) is negative; ξ is introduced as an envelope delay distribution (p.6) and the proof uses E[D_t] ≤ µ + M (p.23)
--   - reading: G_t = Σ_{s=1}^{t−1} 𝕀{s + D_s ≥ t} and T_t = {s ≤ t − 1 : s + D_s ≤ t − 1} → G_t = #{s ∈ [1, t − 1] : s + D_s > t − 1} = (t − 1) − |T_t|; reason: Algorithm 1 (lines 2, 7) sets G_t = (t − 1) − |T_t|; for a fractional delay the printed sum and this count disagree, and the reward of round s is read as arriving at the end of round ⌈s + D_s⌉; for integer delays the two coincide
--   - reading: P(D − µ ≥ x) ≤ exp(−x^{1+q}/(2σ²)) → the inequality for every x ≥ 0, with x^{1+q} the real power; reason: x^{1+q} is not defined for negative x when q is not an integer, and for x < 0 the bound is not meant
--   - encoding: random variables D_t (and features) → measurable functions, non-negativity and the unit-ball bound at every outcome; reason: standing convention of probability; no instance of the paper is excluded up to null-set modification
--   - encoding: with probability (at least) 1 − δ, the bound holds → P(the bound fails) ≤ δ; reason: complement form; for measurable events the two are the same
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, Proposition 1, part 2, (7), p.8

import Mathlib
import Definitions.Def_DelayedGLCB_completeSet
import Definitions.Def_DelayedGLCB_TailEnvelope

namespace DelayedGLCB

open MeasureTheory ProbabilityTheory

/-- **Proposition 1-2 (the running maximum `G*_T`, bound (7)).**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, Proposition 1, part 2, (7), p.8: "With probability `1 − δ`,
`G*_T ≤ 2(µ + M) + σ_G √(2 log T) + 2σ_G² log C₃
 + σ_G √(2 log(1/δ) + 2 log C₃ σ_G √(2 log T) + 2 log C₃) + 1`, (7) where `G*_T = max_{1≤s≤T} G_s`."

For independent non-negative delays `D_1, …, D_T` with tail envelope `(ξ, µ, M)` (Assumption 2),
`T ≥ 1` and `δ > 0`, the probability that `G*_T` exceeds the right side of (7) is at most `δ`.

**Formalization Note.** `G*_T = runMaxMissing D ω T`; `σ_G = sigmaG σ q`, `C₃ = C3 σ`. -/
theorem proposition_1_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (T : ℕ) (ξ : Measure ℝ) (μ M q σ : ℝ) (hM : 0 < M) (hq : 0 ≤ q) (hσ : 0 < σ)
    (hT : 1 ≤ T) (hD : IndepDelays P D T) (hξ : TailEnvelope P D T ξ μ M q σ)
    (δ : ℝ) (hδ : 0 < δ) :
    P {ω | 2 * (μ + M)
        + sigmaG σ q * Real.sqrt (2 * Real.log T) + 2 * sigmaG σ q ^ 2 * Real.log (C3 σ)
        + sigmaG σ q * Real.sqrt (2 * Real.log (1 / δ)
            + 2 * Real.log (C3 σ) * sigmaG σ q * Real.sqrt (2 * Real.log T) + 2 * Real.log (C3 σ))
        + 1 < (runMaxMissing D ω T : ℝ)} ≤ ENNReal.ofReal δ := by sorry

end DelayedGLCB
