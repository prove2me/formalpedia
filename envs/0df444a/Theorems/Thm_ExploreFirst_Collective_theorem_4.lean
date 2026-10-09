-- Prove2me | Theorems.Thm_ExploreFirst_Collective_theorem_4
-- name    : ExploreFirst.Collective.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:47.599452+00:00
-- url     : https://prove2.me/theorems/ebeace9d-2035-4317-a57b-a2a47be00b02
-- title:
--   Theorem 4, p. 13 — symmetric monotonic strategies pull the suboptimal arms at least $T(1-A^\star/K-A^\star\sqrt{2T\mathcal K^{\max}}/K-2A^\star T\mathcal K^{\max}/K)$ times
-- statement:
--   This is the collective lower bound of Garivier, Ménard and Stoltz.
--
--   Let $\mathcal D$ be a model, i.e. a set of probability distributions on $\mathbb R$ with an expectation. Let $\psi$ be a strategy that is pairwise symmetric for optimal arms (Definition 3) and monotonic (Definition 4) on $\mathcal D$, and let $\underline\nu=(\nu_a)_{a=1,\dots,K}$ be a bandit problem in $\mathcal D$ with $K\ge1$ arms. Write $\mathcal A^\star(\underline\nu)$ for its set of optimal arms, $A^\star_{\underline\nu}$ for their number, $\mathcal W(\underline\nu)$ for its set of worst arms, and
--   $$\mathcal K^{\max}_{\underline\nu}=\min_{w\in\mathcal W(\underline\nu)}\ \max_{a^\star\in\mathcal A^\star(\underline\nu)}\mathrm{KL}(\nu_w,\nu_{a^\star}),$$
--   assumed finite. Then for every horizon $T\ge1$, the suboptimal arms are collectively sampled at least
--   $$\sum_{a\notin\mathcal A^\star(\underline\nu)}\mathbb E_{\underline\nu}\big[N_{\psi,a}(T)\big]\ \ge\ T\left(1-\frac{A^\star_{\underline\nu}}K-\frac{A^\star_{\underline\nu}\sqrt{2T\mathcal K^{\max}_{\underline\nu}}}K-\frac{2A^\star_{\underline\nu}T\mathcal K^{\max}_{\underline\nu}}K\right).$$
--
--   With the regret decomposition (1) this gives a regret lower bound that is linear in $T$ as long as $T$ is small compared with $K/(A^\star_{\underline\nu}\mathcal K^{\max}_{\underline\nu})$: the initial "explore first" phase of every reasonable strategy.
--
--   **Formalization Note** Arms are `Fin K` and $K\ge1$ is assumed (the paper has $K\ge1$ throughout). The horizon $T\ge1$ is free in the paper's sentence. $\mathcal K^{\max}$ is valued in $[0,+\infty]$ and assumed finite; when it is $+\infty$ the paper's bound is $-\infty$, so nothing is lost. The paper's "In particular" clause (for $T\le K/(8A^\star\mathcal K^{\max})$, a bound $(T/2)(1-A^\star/K)$) is not part of this statement: it does not follow from the main display when $A^\star/K>1-\sqrt3/2$.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 13, §3.3, Theorem 4 (main display)

import Mathlib
import Definitions.Def_ExploreFirst_Collective_Setting

namespace ExploreFirst.Collective

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal

/-- Theorem 4, p. 13 (main display): for every model `𝒟`, every strategy `ψ` pairwise symmetric
for optimal arms and monotonic on `𝒟`, every bandit problem `ν` in `𝒟` and every `T ≥ 1`,
`∑_{a ∉ 𝒜⋆(ν)} 𝔼_ν[N_a(T)] ≥ T (1 - A⋆/K - A⋆ √(2T𝒦^max)/K - 2A⋆T𝒦^max/K)`,
where `𝒦^max_ν = min_{w ∈ 𝒲(ν)} max_{a⋆ ∈ 𝒜⋆(ν)} KL(ν_w, ν_{a⋆})` is assumed finite. -/
theorem theorem_4 {K : ℕ} (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditPolicy K)
    (hπ : ExploreFirst.Relative.IsPairwiseSymmetric 𝒟 π) (hmono : IsMonotonic 𝒟 π)
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν) (hK : 0 < K) (hfin : kMax ν ≠ ⊤)
    (T : ℕ) (hT : 1 ≤ T) :
    (T : ℝ) * (1 - ((ExploreFirst.Asymptotic.optimalArms ν).card : ℝ) / K
        - ((ExploreFirst.Asymptotic.optimalArms ν).card : ℝ) * Real.sqrt (2 * T * (kMax ν).toReal) / K
        - 2 * ((ExploreFirst.Asymptotic.optimalArms ν).card : ℝ) * T * (kMax ν).toReal / K)
      ≤ ∑ a ∈ (ExploreFirst.Asymptotic.optimalArms ν)ᶜ, ExploreFirst.FundIneq.expPulls ν π T a := by sorry

end ExploreFirst.Collective
