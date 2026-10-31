-- Prove2me | Theorems.Thm_CompInvestBayes_proposition_2_b
-- name    : CompInvestBayes.proposition_2_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:43.066365+00:00
-- url     : https://prove2.me/theorems/89acf8e9-dac2-4899-8600-bf2a75e260e3
-- title:
--   Proposition 2(b) — for $S_1\in(0,\mu_L]$ immediate investment of $S^*_2$ is optimal
-- statement:
--   Let the standing assumptions hold, $\sigma>0$, $S_1\in(0,\mu_L]$ and $y_0\in[0,1]$. Investing at $t=0$ the size
--
--   $$
--   S^*_2=\begin{cases}\mu_{2,L} & y_0\in[0,c_2\lambda],\\ \mu_{2,H} & y_0\in(c_2\lambda,1]\end{cases}
--   $$
--
--   is a feasible strategy of the follower and a best response.
--
--   For such sizes the leader's earnings carry no information about $\theta$, so waiting only costs discounting.
--
--   Differences from the source:
--   - reading: 'invest ... at t = 0 with probability 1' → the strategy τ ≡ 0, S₂ ≡ S*₂(y₀) is feasible and a best response; reason: the stated strategy invests at 0 on every path, in particular with probability 1
--   - generalization: one fixed probability space (Ω, F, P) → every probability space satisfying the model's assumptions (Setup); reason: the paper's space is one such space, so the statement specializes to it
--   - encoding: a probability space with Brownian motions, a binary θ with P(θ = 1) = π₀, Itô integrals, the augmented natural filtration of X^s_1 → the Setup structure (θ = 1{U < y₀} from an independent uniform U), the pathwise integration-by-parts discounted integral discInt, Mathlib's raw natural filtration, stopping times in [0, ∞], F_τ-measurable S₂ ≥ 0; reason: the conventions of the mission's definitions; each realizes the paper's object (see the definitions' Formalization Notes and MODERATION_NOTES.md)
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), Proposition 2(b), p.12 (PDF 12)

import Mathlib
import Definitions.Def_CompInvestBayes_gImmediate

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

/-- **Proposition 2(b)** (SSRN 3408260, p.12, PDF 12). For any leader size `S₁ ∈ (0, µ_L]` and
prior `y₀ ∈ [0, 1]`, it is optimal for the follower to invest at `t = 0` the size
`S*₂ = µ_{2,L}` if `y₀ ∈ [0, c₂λ]` and `µ_{2,H}` if `y₀ ∈ (c₂λ, 1]`: the strategy `τ ≡ 0`,
`S₂ ≡ S*₂` is feasible and optimal. -/
theorem proposition_2_b (p : Params) (hp : p.Standing) {σ : ℝ} (hσ : 0 < σ)
    {Ω : Type*} [MeasurableSpace Ω] (E : Setup Ω) {S1 y0 : ℝ} (hS1 : 0 < S1)
    (hS1' : S1 ≤ p.muL) (hy0 : y0 ∈ Set.Icc (0 : ℝ) 1) :
    ∃ s : FollowerStrategy p σ E S1 y0,
      (∀ ω, s.τ ω = 0) ∧ (∀ ω, s.S2 ω = S2star p y0) ∧ IsFollowerOptimal s := by sorry

end CompInvestBayes
