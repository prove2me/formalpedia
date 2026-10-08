-- Prove2me | Theorems.Thm_AgrawalGoyalTS_NArmed_saturated_regret_interval_le
-- name    : AgrawalGoyalTS.NArmed.saturated_regret_interval_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:06:00.422981+00:00
-- url     : https://prove2.me/theorems/549e28dd-bd27-4590-b59a-11c7e01be63f
-- title:
--   Lemma 5 — regret from saturated arms between consecutive plays of the optimal arm, Eq. (7)
-- statement:
--   Consider Thompson Sampling (Algorithm 2) on $N$ arms with rewards supported in $[0,1]$ and arm $1$ the unique optimal arm, run for $T$ rounds. Let $I_j$ be the interval between the $j$-th and $(j+1)$-th plays of arm $1$, $\gamma_j$ the number of rounds $t\in I_j$ at which $M(t)$ holds ($\theta_1(t)$ exceeds $\mu_i+\Delta_i/2$ for every saturated arm $i$), $I_j(1),\dots,I_j(\gamma_j+1)$ the pieces into which these rounds cut $I_j$, and $V_j^{\ell,a}$ the number of rounds of $I_j(\ell)$ at which $a$ is the best saturated arm. Let $s(j)$ be the number of successes in the first $j$ plays of arm $1$, and $X(j,s,y)$ the number of trials before an independent $\mathrm{Beta}(s+1,j-s+1)$ sequence exceeds $y$. Then for every $j$,
--
--   $$\mathbb E\Big[\sum_{\ell=1}^{\gamma_j+1}\sum_a V_j^{\ell,a}\Delta_a\Big]\le\mathbb E\Big[\mathbb E\big[\gamma_j+1\,\big|\,s(j)\big]\sum_{a=2}^{N}\Delta_a\,\mathbb E\Big[\min\Big\{X\Big(j,s(j),\mu_a+\frac{\Delta_a}{2}\Big),T\Big\}\,\Big|\,s(j)\Big]\Big].$$
--
--   Because $s(j)$ takes only the values $0,\dots,j$, the right side equals
--   $$\sum_{s=0}^{j}\mathbb E\big[(\gamma_j+1)\,\mathbf 1\{s(j)=s\}\big]\sum_{a=2}^{N}\Delta_a\,\mathbb E\Big[\min\Big\{X\Big(j,s,\mu_a+\frac{\Delta_a}{2}\Big),T\Big\}\Big],$$
--   which is the form stated in Lean. The lemma bounds the regret from saturated arms inside one interval between plays of the optimal arm by a product of the number of $M$-occurrences and a waiting time of the optimal arm's posterior samples.
--
--   **Formalization Note** The conditional expectations are given $s(j)$ only, and $X(j,s,y)$ given $s(j)=s$ is an independent geometric count, so $\mathbb E[\cdot\mid s(j)]$ is written as a finite sum over the values of $s(j)$ with no division. Expectations are lower Lebesgue integrals in $[0,\infty]$. The sums over $a$ run over the suboptimal arms ($a\ne 1$). If arm $1$ is not played a $(j+1)$-th time within the horizon, $I_j$ runs to the horizon.
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 10, Lemma 5, Eq. (7) (proof in App. C.5, pp. 19–20)

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_AgrawalGoyalTS_NArmed_BetaBinomial
import Definitions.Def_AgrawalGoyalTS_NArmed_ThompsonSampling
import Definitions.Def_AgrawalGoyalTS_NArmed_Saturation

open MeasureTheory BanditAlgorithm

namespace AgrawalGoyalTS.NArmed

/-- Lemma 5 (p. 10), Eq. (7): `N` arms with rewards supported in `[0,1]`, arm `0` (the paper's
arm 1) the unique optimal arm, horizon `T`. For every `j`,
`E[∑_{ℓ=1}^{γ_j+1} ∑_a V_j^{ℓ,a} Δ_a]
  ≤ E[ E[γ_j + 1 | s(j)] ∑_{a ≠ 1} Δ_a E[min{X(j, s(j), μ_a + Δ_a/2), T} | s(j)] ]`.
Since `s(j)` takes the values `0, …, j`, the right side is written as
`∑_s E[(γ_j + 1) 1{s(j) = s}] · ∑_a Δ_a E[min{X(j, s, μ_a + Δ_a/2), T}]`, where `X(j, s, y)`
counts the trials before an i.i.d. `Beta(s+1, j-s+1)` sequence exceeds `y`. -/
theorem saturated_regret_interval_le {N : ℕ} [NeZero N] (ν : StochasticBandit N)
    (hsupp : ∀ i, ν.P i (Set.Icc 0 1) = 1)
    (hopt : ∀ i, i ≠ 0 → banditArmMean ν i < banditArmMean ν 0) (T j : ℕ) :
    ∫⁻ ω, ∑ ℓ ∈ Finset.Icc 1 (gammaCount ν T ω j + 1),
        ∑ a ∈ Finset.univ.filter (fun a : Fin N => a ≠ 0),
          (Vcount ν T ω j ℓ a : ENNReal) * ENNReal.ofReal (gapTo0 ν a) ∂(AgrawalGoyalTS.TwoArmed.tsLaw ν) ≤
      ∑ s ∈ Finset.range (j + 1),
        (∫⁻ ω in {ω | stackSuccesses ω 0 j = s},
            ((gammaCount ν T ω j : ENNReal) + 1) ∂(AgrawalGoyalTS.TwoArmed.tsLaw ν)) *
          ∑ a ∈ Finset.univ.filter (fun a : Fin N => a ≠ 0),
            ENNReal.ofReal (gapTo0 ν a) *
              ∫⁻ w, min (ENat.toENNReal
                  (AgrawalGoyalTS.TwoArmed.firstExceed (banditArmMean ν a + gapTo0 ν a / 2) w)) (T : ENNReal)
                ∂(AgrawalGoyalTS.TwoArmed.betaTrials s (j - s)) := by sorry

end AgrawalGoyalTS.NArmed
