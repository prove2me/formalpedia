-- Prove2me | Theorems.Thm_ExploreFirst_Relative_theorem_3
-- name    : ExploreFirst.Relative.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:40.791039+00:00
-- url     : https://prove2.me/theorems/6e529ab2-0afa-4a63-aa62-0a713707463a
-- title:
--   Theorem 3, p. 11 — under pairwise symmetry, 𝔼[N_a(T)] ≥ T/K or 𝔼[N⁺_a/N⁺_{a⋆}] ≥ 1 − 2√(2T KL(ν_a, ν_{a⋆})/K)
-- statement:
--   **Theorem 3 (relative lower bound).** Let $\mathcal{D}$ be a model, i.e. a set of distributions on $\mathbb{R}$ with an expectation. Let $\psi$ be a strategy that is pairwise symmetric for optimal arms on $\mathcal{D}$: for every bandit problem in $\mathcal{D}$ and every pair of optimal arms with the same distribution, the pair of their pull counts and the swapped pair have the same joint law at every horizon $T \ge 1$. Let $\underline{\nu} = (\nu_1, \dots, \nu_K)$ be a bandit problem in $\mathcal{D}$, let $a$ be a suboptimal arm and $a^\star$ an optimal arm of $\underline{\nu}$, and suppose $\mathrm{KL}(\nu_a, \nu_{a^\star}) < +\infty$. Then for every $T \ge 1$,
--   $$\text{either}\quad \mathbb{E}_{\underline{\nu}}\big[N_{\psi,a}(T)\big] \ge \frac{T}{K} \quad\text{or}\quad \mathbb{E}_{\underline{\nu}}\left[\frac{\max\{N_{\psi,a}(T), 1\}}{\max\{N_{\psi,a^\star}(T), 1\}}\right] \ge 1 - 2\sqrt{\frac{2T\,\mathrm{KL}(\nu_a, \nu_{a^\star})}{K}} .$$
--   Here $N_{\psi,k}(T)$ is the number of pulls of arm $k$ in the first $T$ rounds and $\mathbb{E}_{\underline{\nu}}$ is the expectation when $\psi$ plays against $\underline{\nu}$.
--
--   In the small-horizon regime the theorem says that a reasonable strategy cannot neglect a suboptimal arm: either it pulls the arm as often as the uniform strategy does, or on average it pulls it nearly as often as an optimal arm. The bound depends only on the divergence between the suboptimal and the optimal arm distributions, not on the model's $\mathcal{K}_{\inf}$.
--
--   **Formalization Note** The finiteness of $\mathrm{KL}(\nu_a,\nu_{a^\star})$ is added: when it is $+\infty$ the printed second alternative reads $\ge -\infty$ and the statement is empty, while treating $+\infty$ as the real number $0$ would make the bound false. Arms are $0$-based, strategies are kernel policies (`BanditPolicy`), and the ratio is the Bochner integral of a function bounded by $T$, hence integrable. The disjunction is kept exactly as printed.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 11, Theorem 3 (first display); proof p. 12

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_ExploreFirst_Relative_Setting

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace ExploreFirst.Relative

theorem theorem_3 {K : ℕ} (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟)
    (π : BanditPolicy K) (hπ : IsPairwiseSymmetric 𝒟 π)
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a a' : Fin K) (ha : 0 < banditGap ν a) (ha' : a' ∈ ExploreFirst.Asymptotic.optimalArms ν)
    (hKL : InformationTheory.klDiv (ν.P a) (ν.P a') ≠ ⊤)
    (T : ℕ) (hT : 1 ≤ T) :
    (T : ℝ) / K ≤ ExploreFirst.FundIneq.expPulls ν π T a ∨
      1 - 2 * Real.sqrt (2 * (T : ℝ) * (InformationTheory.klDiv (ν.P a) (ν.P a')).toReal / K) ≤
        ∫ h, max (armPullCount a h : ℝ) 1 / max (armPullCount a' h : ℝ) 1
          ∂(banditMeasure ν π T) := by sorry

end ExploreFirst.Relative
