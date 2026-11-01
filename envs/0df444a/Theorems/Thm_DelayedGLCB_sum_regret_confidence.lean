-- Prove2me | Theorems.Thm_DelayedGLCB_sum_regret_confidence
-- name    : DelayedGLCB.sum_regret_confidence
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:55.028063+00:00
-- url     : https://prove2.me/theorems/d7c5b82f-d46f-45b7-8467-52d65d357eb4
-- title:
--   Proof of Theorem 1, p.27 — summed regret on the confidence event (corrected: the third step, false at $d=1$, is omitted)
-- statement:
--   Run DUCB-GLCB with an arg max tie-break, $\hat\sigma>0$, $\kappa>0$, and fix an outcome at which every feature vector lies in the unit ball. Let $1\le d\le T$, suppose $\lambda_{\min}(V_{\tau+1})\ge1$ and $\|\hat\theta_t-\theta^*\|_{V_t}\le\beta_t$ for every $t\in(\tau,T]$, and let $b_t$ be any arms, $X^*_t=x_{t,b_t}$. Then
--   $$
--   \sum_{t=\tau+1}^{T}\big(\langle X^*_t,\theta^*\rangle-\langle X_t,\theta^*\rangle\big)\le2\max_{1\le t\le T}\beta_t\sqrt{2Td\log(T/d)}
--   $$
--   and
--   $$
--   2\max_{1\le t\le T}\beta_t\sqrt{2Td\log(T/d)}\le2\Big[\frac{\hat\sigma}{\kappa}\sqrt{\frac d2\log\Big(1+\frac{2T}{d}\Big)+\log\frac1\delta}+\sqrt{G^*_T}\Big]\sqrt{2Td\log(T/d)}.
--   $$
--
--   This combines (40) and (41) into a bound on the linear part of the regret in terms of $G^*_T$, which Proposition 1-2 controls.
--
--   Differences from the source:
--   - generalization: the optimal arm a*_t, X*_t = x_{t,a*_t} → any comparator arm b, X*_t = x_{t,b}; reason: the step never uses optimality of a*_t; a*_t is an instance
--   - reading: the event E_t (not defined on the page) → ‖θ̂_t − θ*‖_{V_t} ≤ β_t; reason: E_t is the confidence event that (37) establishes, the hypothesis used to pass from (36) to (40)
--   - generalization: λ_min(W_{τ+1}) ≥ 1 (supposition of p.26) → λ_min(V_{τ+1}) ≥ 1; reason: V_{τ+1} ⪰ W_{τ+1}, so the paper's supposition implies it
--   - correction: third step: … ≤ 2√G*_T √(2Td log(T/d)) + (2dσ̂/κ) log(T/(dδ)) √T → not stated; reason: false at d = 1: with δ = 0.1, log T = 20, G*_T = 0 (no delays) the left side divided by 2σ̂√T/κ is √(½ log(1+2T) + log 10)·√(2 log T) = 22.49, the right side log(10T) = 22.30
--   - encoding: max_{1≤t≤T} β_t → the supremum of β_t over the nonempty finite set [1, T]; reason: equal to the maximum since T ≥ d ≥ 1
--   - encoding: a_t = arg max_a (x'_{t,a}θ̂_t + β_t‖x_{t,a}‖_{V_t^{-1}}) → a deterministic tie-break tie with v b ≤ v (tie v) for all b; reason: any arg max rule is such a tie-break
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, proof of Theorem 1, p.27 (display after (41), first two steps)

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Matrix
import Definitions.Def_DelayedGLCB_DUCB

namespace DelayedGLCB

open Matrix MostlyExplorationFree.GreedyBandit

/-- **Summed regret on the confidence event (p.27, first two steps).**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, proof of Theorem 1, p.27: "Combine (40) and (41), we have
`Σ_{t=τ+1}^T (⟨X*_t, θ*⟩ − ⟨X_t, θ*⟩) ≤ 2 max_{1≤t≤T}{β_t} √(2Td log(T/d))
 ≤ 2 [ (σ̂/κ) √((d/2) log(1 + 2T/d) + log(1/δ)) + √G*_T ] √(2Td log(T/d))`."

For every outcome `ω` at which all feature vectors lie in the unit ball, with `σ̂, κ > 0`,
`1 ≤ d ≤ T`, `λ_min(V_{τ+1}) ≥ 1` and `‖θ̂_t − θ*‖_{V_t} ≤ β_t` for every `t ∈ (τ, T]`, and for any
comparator arms `b_t`, the run of DUCB-GLCB (argmax tie-break) satisfies both inequalities.

**Formalization Note.** Only the first two steps of the display are stated: its third step,
`… ≤ 2√G*_T √(2Td log(T/d)) + (2dσ̂/κ) log(T/(dδ)) √T`, fails at `d = 1` (for `δ = 0.1`,
`log T = 20`, `G*_T = 0`: `22.49 > 22.30` after dividing by `2σ̂√T/κ`). `max_{1≤t≤T}` is a supremum over
the nonempty finite set `[1, T]`. Any comparator arms are allowed in place of `a*_t`. -/
theorem sum_regret_confidence {Ω : Type*} {d K : ℕ} (A : DUCB d K) (E : Env Ω d K) (ω : Ω)
    (θstar : Fin d → ℝ) (hA : IsArgmaxSelector A.tie) (hκ : 0 < A.κ) (hσhat : 0 < A.σhat)
    (hd : 1 ≤ d) (T : ℕ) (hT : d ≤ T) (hx : ∀ s a, l2norm (E.x s ω a) ≤ 1)
    (hV : 1 ≤ lambdaMin (V A E ω (A.τ + 1)))
    (hconf : ∀ t ∈ Finset.Ioc A.τ T,
      wnorm (V A E ω t) (thetaHat A E ω t - θstar) ≤ betaAt A E ω t)
    (b : ℕ → Fin K) :
    (∑ t ∈ Finset.Ioc A.τ T, (E.x t ω (b t) ⬝ᵥ θstar - X A E ω t ⬝ᵥ θstar)
        ≤ 2 * (⨆ t : Finset.Icc 1 T, betaAt A E ω t)
          * Real.sqrt (2 * T * d * Real.log ((T : ℝ) / d))) ∧
    2 * (⨆ t : Finset.Icc 1 T, betaAt A E ω t) * Real.sqrt (2 * T * d * Real.log ((T : ℝ) / d))
      ≤ 2 * (A.σhat / A.κ * Real.sqrt ((d : ℝ) / 2 * Real.log (1 + 2 * (T : ℝ) / d)
              + Real.log (1 / A.δ))
            + Real.sqrt (runMaxMissing E.D ω T))
          * Real.sqrt (2 * T * d * Real.log ((T : ℝ) / d)) := by sorry

end DelayedGLCB
