-- Prove2me | Theorems.Thm_ExploreFirst_Relative_equation_12
-- name    : ExploreFirst.Relative.equation_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:57.504866+00:00
-- url     : https://prove2.me/theorems/f862d638-1734-430a-b16d-80b7c3db6e62
-- title:
--   (12), p. 12 — 𝔼_ν̲[N_a(T)] KL(ν_a, ν′_a) ≥ kl(𝔼_ν̲[N⁺_a/(N⁺_a + N⁺_{a⋆})], 1/2)
-- statement:
--   Under the hypotheses of the symmetry identity (a model $\mathcal{D}$, a strategy $\psi$ pairwise symmetric for optimal arms on $\mathcal{D}$, a bandit problem $\underline{\nu}$ in $\mathcal{D}$, a suboptimal arm $a$, an optimal arm $a^\star$, the alternative $\underline{\nu}'$ with $\nu'_k = \nu_k$ for $k \ne a$ and $\nu'_a = \nu_{a^\star}$, and $T \ge 1$),
--   $$\mathbb{E}_{\underline{\nu}}\big[N_{\psi,a}(T)\big]\,\mathrm{KL}(\nu_a, \nu'_a) \;\ge\; \mathrm{kl}\left(\mathbb{E}_{\underline{\nu}}\left[\frac{N^+_{\psi,a}(T)}{N^+_{\psi,a}(T) + N^+_{\psi,a^\star}(T)}\right], \frac12\right),$$
--   where $\mathrm{kl}$ is the Bernoulli Kullback–Leibler divergence (5) and $N^+_{\psi,k}(T) = \max\{N_{\psi,k}(T), 1\}$.
--
--   This is the fundamental inequality (6) applied with $Z = N^+_{\psi,a}(T)/(N^+_{\psi,a}(T) + N^+_{\psi,a^\star}(T))$, a $[0,1]$-valued function of the history, combined with $\mathbb{E}_{\underline{\nu}'}[Z] = 1/2$. Only arm $a$ differs between $\underline{\nu}$ and $\underline{\nu}'$, so the left side of (6) reduces to one term.
--
--   **Formalization Note** Both sides are in $[0, +\infty]$: the Kullback–Leibler divergence $\mathrm{KL}(\nu_a,\nu'_a)$ may be $+\infty$, and the expected pull count is embedded as a nonnegative extended real.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 12, (12)

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_ExploreFirst_Relative_Setting

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace ExploreFirst.Relative

theorem equation_12 {K : ℕ} (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟)
    (π : BanditPolicy K) (hπ : IsPairwiseSymmetric 𝒟 π)
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a a' : Fin K) (ha : 0 < banditGap ν a) (ha' : a' ∈ ExploreFirst.Asymptotic.optimalArms ν)
    (ν' : StochasticBandit K) (hν'_ne : ∀ k, k ≠ a → ν'.P k = ν.P k) (hν'_a : ν'.P a = ν.P a')
    (T : ℕ) (hT : 1 ≤ T) :
    ExploreFirst.FundIneq.klBer (∫ h, pullsPlus a h / (pullsPlus a h + pullsPlus a' h) ∂(banditMeasure ν π T)) (1 / 2) ≤
      ENNReal.ofReal (ExploreFirst.FundIneq.expPulls ν π T a) * InformationTheory.klDiv (ν.P a) (ν'.P a) := by sorry

end ExploreFirst.Relative
