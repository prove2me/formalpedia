-- Prove2me | Theorems.Thm_ExploreFirst_Collective_monotone_reduction
-- name    : ExploreFirst.Collective.monotone_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:06:04.369219+00:00
-- url     : https://prove2.me/theorems/88ee0e1e-6c8d-41c8-aae8-f96b1f6084c4
-- title:
--   Proof of Theorem 4, p. 13 — by monotonicity, moving the suboptimal arms to a worst arm can only lower their pull counts
-- statement:
--   Let $\mathcal D$ be a model of distributions with an expectation, $\psi$ a strategy monotonic on $\mathcal D$ (Definition 4), and $\underline\nu$ a bandit problem in $\mathcal D$. Let $\tilde w\in\mathcal W(\underline\nu)$ be a worst arm and let $\underline{\underline\nu}$ be the bandit problem that agrees with $\underline\nu$ on the optimal arms and carries $\nu_{\tilde w}$ on every other arm:
--   $$\underline{\underline\nu}_a=\nu_a\ \ (a\in\mathcal A^\star(\underline\nu)),\qquad \underline{\underline\nu}_a=\nu_{\tilde w}\ \ (a\notin\mathcal A^\star(\underline\nu)).$$
--   Then for all $T\ge1$,
--   $$\sum_{a\notin\mathcal A^\star(\underline\nu)}\mathbb E_{\underline\nu}\big[N_{\psi,a}(T)\big]\ \ge\ \sum_{a\notin\mathcal A^\star(\underline{\underline\nu})}\mathbb E_{\underline{\underline\nu}}\big[N_{\psi,a}(T)\big].$$
--
--   The problem $\underline{\underline\nu}$ is in $\mathcal D$ and satisfies $\underline{\underline\nu}\preccurlyeq\underline\nu$, so this is the first step of the proof of Theorem 4: it reduces the bound on $\underline\nu$ to a bound on the easier problem $\underline{\underline\nu}$.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 13, §3.3, proof of Theorem 4, display after "By monotonicity of ψ"

import Mathlib
import Definitions.Def_ExploreFirst_Collective_Setting

namespace ExploreFirst.Collective

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal

/-- Proof of Theorem 4, p. 13: for a worst arm `w` of `ν`, let `ν̳` agree with `ν` on the optimal
arms of `ν` and carry `ν_w` on every other arm. By monotonicity of `ψ`,
`∑_{a ∉ 𝒜⋆(ν)} 𝔼_ν[N_a(T)] ≥ ∑_{a ∉ 𝒜⋆(ν̳)} 𝔼_ν̳[N_a(T)]`. -/
theorem monotone_reduction {K : ℕ} (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditPolicy K)
    (hmono : IsMonotonic 𝒟 π) (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (w : Fin K) (hw : w ∈ worstArms ν)
    (νdd : StochasticBandit K)
    (hνdd : ∀ a, νdd.P a = if a ∈ ExploreFirst.Asymptotic.optimalArms ν then ν.P a else ν.P w)
    (T : ℕ) (hT : 1 ≤ T) :
    ∑ a ∈ (ExploreFirst.Asymptotic.optimalArms νdd)ᶜ, ExploreFirst.FundIneq.expPulls νdd π T a ≤ ∑ a ∈ (ExploreFirst.Asymptotic.optimalArms ν)ᶜ, ExploreFirst.FundIneq.expPulls ν π T a := by sorry

end ExploreFirst.Collective
