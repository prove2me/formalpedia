-- Prove2me | Theorems.Thm_AgrawalGoyalTS_TwoArmed_prob_E2_ge
-- name    : AgrawalGoyalTS.TwoArmed.prob_E2_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:27:31.400638+00:00
-- url     : https://prove2.me/theorems/8a7ee1c0-6da3-4a8a-b16e-9680cf4dd514
-- title:
--   Lemma 2 — Pr(E₂(t)) ≥ 1 − 2/T²
-- statement:
--   Consider Thompson Sampling (Algorithm 2) on a two-armed bandit whose reward distributions are supported in $[0,1]$, with means $\mu_1>\mu_2$ (arm 1 is the unique optimal arm), and let $\Delta=\mu_1-\mu_2$. Fix a horizon $T$ and put $L=24(\ln T)/\Delta^2$. For a round $t$ let $\theta_2(t)$ be the posterior sample of arm 2 and $k_2(t)$ the number of plays of arm 2 before round $t$, and let
--   $$E_2(t)=\Big\{\theta_2(t)\le\mu_2+\tfrac{\Delta}{2}\ \text{ or }\ k_2(t)<L\Big\}.$$
--   Then for every round $t\in\{1,\dots,T\}$,
--   $$\Pr(E_2(t))\ge 1-\frac{2}{T^2}.$$
--
--   The event $E_2(t)$ says that once arm 2 has been played enough, its posterior sample is not much larger than its mean; Lemma 2 bounds the total contribution of its failure to the expected number of plays of arm 2.
--
--   **Formalization Note** Arm 1 of the paper is Lean arm `0`, arm 2 is Lean arm `1`, and paper round $t$ is Lean round $t-1$, so "every $t\in\{1,\dots,T\}$" is `t < T`. The real threshold $L$ is compared with the cast count, without rounding.
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 7, Lemma 2 (event E2(t) defined just above it; L defined on p. 6)

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_AgrawalGoyalTS_TwoArmed_ThompsonSampling

open MeasureTheory BanditAlgorithm

namespace AgrawalGoyalTS.TwoArmed

/-- Lemma 2 (p. 7): two arms with rewards supported in `[0,1]`, arm `0` (the paper's arm 1)
strictly better than arm `1` (the paper's arm 2), `Δ = μ₁ - μ₂`, `L = 24 ln T / Δ²`. For every
round `t` of the horizon `T` (Lean rounds `t < T`), the event
`E₂(t) = {θ₂(t) ≤ μ₂ + Δ/2 or k₂(t) < L}` has probability at least `1 - 2/T²` under Thompson
Sampling (Algorithm 2). -/
theorem prob_E2_ge (ν : StochasticBandit 2) (hsupp : ∀ i, ν.P i (Set.Icc 0 1) = 1)
    (hopt : banditArmMean ν 1 < banditArmMean ν 0) (T t : ℕ) (ht : t < T) :
    ENNReal.ofReal (1 - 2 / (T : ℝ) ^ 2) ≤
      tsLaw ν {ω | tsTheta ω t 1 ≤
          banditArmMean ν 1 + (banditArmMean ν 0 - banditArmMean ν 1) / 2 ∨
        (tsPlays ω t 1 : ℝ) <
          24 * Real.log T / (banditArmMean ν 0 - banditArmMean ν 1) ^ 2} := by sorry

end AgrawalGoyalTS.TwoArmed
