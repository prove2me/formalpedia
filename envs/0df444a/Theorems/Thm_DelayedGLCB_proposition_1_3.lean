-- Prove2me | Theorems.Thm_DelayedGLCB_proposition_1_3
-- name    : DelayedGLCB.proposition_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:09.171806+00:00
-- url     : https://prove2.me/theorems/7c6b00e8-6ecc-4a59-9b76-0dae3354e49f
-- title:
--   Proposition 1-3 — $\lambda_{\min}(W_t)\ge B$ with probability $1-2\delta$ once $t$ exceeds (8) (corrected: envelope $\xi$ on $[0,\infty)$)
-- statement:
--   There are absolute constants $C_1,C_2>0$ with the following property. Let $d\ge1$, let $X_1,X_2,\dots$ be i.i.d. random vectors in the unit ball of $\mathbb R^d$, independent of delays $D_1,\dots,D_T$ that satisfy Assumption 2 with $M>0$, $q\ge0$, $\sigma>0$. Let $\Sigma=\mathbb E[X_1X_1']$ with $\lambda_{\min}(\Sigma)>0$, $B>0$, $\delta>0$, and $W_t=\sum_{s\in T_t}X_sX_s'$. For every $t\in[1,T]$ with
--   $$
--   t\ge\Big(\frac{C_1\sqrt d+C_2\sqrt{\log(1/\delta)}}{\lambda_{\min}(\Sigma)}\Big)^2+\frac{2B}{\lambda_{\min}(\Sigma)}+2(\mu+M)+\sigma_G\sqrt{2\log\tfrac1\delta}+2\sigma_G^2\log C_3+1,
--   $$
--   we have $P(\lambda_{\min}(W_t)<B)\le2\delta$.
--
--   Despite missing rewards, the matrix of complete samples becomes well conditioned after a number of rounds that is linear in $d+\log(1/\delta)$ plus the delay terms. This is what fixes the length $\tau$ of the exploration phase.
--
--   Differences from the source:
--   - correction: ξ a distribution with mean µ < ∞ → ξ a probability measure on [0, ∞) with finite mean µ; reason: over all of ℝ the statement is false: ξ = point mass at −100 (µ = −100), M = 10, σ = 0.1, q = 0, D_t ≡ 9.5 satisfy every clause of Assumption 2, yet G_t ≥ 9 for t ≥ 10 while the right side of (6) is negative; ξ is introduced as an envelope delay distribution (p.6) and the proof uses E[D_t] ≤ µ + M (p.23)
--   - reading: G_t = Σ_{s=1}^{t−1} 𝕀{s + D_s ≥ t} and T_t = {s ≤ t − 1 : s + D_s ≤ t − 1} → G_t = #{s ∈ [1, t − 1] : s + D_s > t − 1} = (t − 1) − |T_t|; reason: Algorithm 1 (lines 2, 7) sets G_t = (t − 1) − |T_t|; for a fractional delay the printed sum and this count disagree, and the reward of round s is read as arriving at the end of round ⌈s + D_s⌉; for integer delays the two coincide
--   - reading: P(D − µ ≥ x) ≤ exp(−x^{1+q}/(2σ²)) → the inequality for every x ≥ 0, with x^{1+q} the real power; reason: x^{1+q} is not defined for negative x when q is not an integer, and for x < 0 the bound is not meant
--   - encoding: λ_min(A), the smallest eigenvalue → lambdaMin A, the infimum of v'Av over unit vectors; reason: equal for symmetric matrices, which are the only ones it is applied to
--   - encoding: (8) with λ_min(Σ) in the denominator → hypothesis λ_min(Σ) > 0; reason: (8) divides by λ_min(Σ); the condition only excludes the undefined case
--   - reading: X_t drawn iid from γ; delays as in Assumption 2 → (X_t)_{t≥1} i.i.d., and the families (X_t) and (D_t) independent; reason: the delays are independent of the features (p.5); without it the random set T_t could select ill-conditioned samples
--   - encoding: for every t (horizon of Assumption 2 unstated) → t ∈ [1, T] for the horizon T of Assumption 2; reason: W_t uses only D_s with s < t; T is arbitrary
--   - encoding: random variables D_t (and features) → measurable functions, non-negativity and the unit-ball bound at every outcome; reason: standing convention of probability; no instance of the paper is excluded up to null-set modification
--   - encoding: with probability (at least) 1 − 2δ, the bound holds → P(the bound fails) ≤ 2δ; reason: complement form; for measurable events the two are the same
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, Proposition 1, part 3, (8), p.8

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Matrix
import Definitions.Def_DelayedGLCB_Vmat
import Definitions.Def_DelayedGLCB_TailEnvelope

universe u

namespace DelayedGLCB

open MeasureTheory ProbabilityTheory MostlyExplorationFree.GreedyBandit

/-- **Proposition 1-3 (the complete-sample matrix becomes well conditioned, (8)).**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, Proposition 1, part 3, (8), p.8: "Define
`W_t = Σ_{s∈T_t} X_s X_s'` where `X_t` is drawn iid. from some distribution `γ` with support in the unit
ball `B_d`. Furthermore, let `Σ := E[X_t X_t']` be the second moment matrix, and `B` and `δ > 0` be two
positive constants. Then there exist positive, universal constants `C₁` and `C₂` such that
`λ_min(W_t) ≥ B` with probability at least `1 − 2δ`, as long as
`t ≥ ((C₁√d + C₂√(log(1/δ)))/λ_min(Σ))² + 2B/λ_min(Σ) + 2(µ + M) + σ_G √(2 log(1/δ)) + 2σ_G² log C₃ + 1`."

There are absolute constants `C₁, C₂ > 0` such that: for every `d ≥ 1`, every i.i.d. sequence
`X_1, X_2, …` in the unit ball of `ℝ^d`, independent of delays `D_1, …, D_T` satisfying Assumption 2,
with `Σ = E[X_1 X_1']`, `λ_min(Σ) > 0`, every `B > 0`, `δ > 0` and every `t ∈ [1, T]` at least the
right side of (8), `P(λ_min(W_t) < B) ≤ 2δ`.

**Formalization Note.** `C₁, C₂` are chosen before every other object ("universal"). `λ_min` is the
Rayleigh infimum `lambdaMin`; `λ_min(Σ) > 0` is assumed because (8) divides by it. The i.i.d.
sequence is indexed by `t ≥ 1`; "independent of the delays" is independence of the two whole
families. The delays are needed up to `t − 1 < T`. -/
theorem proposition_1_3 : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ)
      (X : ℕ → Ω → Fin d → ℝ) (D : ℕ → Ω → ℝ) (T : ℕ) (ξ : Measure ℝ) (μ M q σ B δ : ℝ),
      1 ≤ d → 0 < M → 0 ≤ q → 0 < σ →
      IndepDelays P D T → TailEnvelope P D T ξ μ M q σ →
      (∀ t, Measurable (X t)) → (∀ t ω, l2norm (X t ω) ≤ 1) →
      iIndepFun (fun t : {t : ℕ // 1 ≤ t} => X t) P →
      (∀ t, 1 ≤ t → IdentDistrib (X t) (X 1) P P) →
      IndepFun (fun ω (t : {t : ℕ // 1 ≤ t}) => X t ω) (fun ω (t : {t : ℕ // 1 ≤ t}) => D t ω) P →
      0 < lambdaMin (Matrix.of fun i j => ∫ ω, X 1 ω i * X 1 ω j ∂P) →
      0 < B → 0 < δ →
      ∀ t ∈ Finset.Icc 1 T,
        ((C₁ * Real.sqrt d + C₂ * Real.sqrt (Real.log (1 / δ)))
              / lambdaMin (Matrix.of fun i j => ∫ ω, X 1 ω i * X 1 ω j ∂P)) ^ 2
          + 2 * B / lambdaMin (Matrix.of fun i j => ∫ ω, X 1 ω i * X 1 ω j ∂P)
          + 2 * (μ + M)
          + sigmaG σ q * Real.sqrt (2 * Real.log (1 / δ)) + 2 * sigmaG σ q ^ 2 * Real.log (C3 σ)
          + 1 ≤ (t : ℝ) →
        P {ω | lambdaMin (Wmat D ω (fun s => X s ω) t) < B} ≤ ENNReal.ofReal (2 * δ) := by sorry

end DelayedGLCB
