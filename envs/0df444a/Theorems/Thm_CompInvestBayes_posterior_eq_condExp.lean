-- Prove2me | Theorems.Thm_CompInvestBayes_posterior_eq_condExp
-- name    : CompInvestBayes.posterior_eq_condExp
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:06:12.834177+00:00
-- url     : https://prove2.me/theorems/a984a1f1-1c56-4618-b5ad-6308363c1377
-- title:
--   Posterior belief: the Bayes-formula process is $\mathbb P(\theta=1\mid\mathcal F^{X^s_1}_t)$
-- statement:
--   Let the standing assumptions hold, $\sigma>0$, the leader's size $S_1\ge0$ and the prior $y_0\in[0,1]$. For every time $t\ge0$, the posterior process $\pi_t=y_0L_t/(y_0L_t+1-y_0)$ is almost surely equal to the conditional probability of a favorable market given the follower's information:
--
--   $$
--   \pi_t=\mathbb P\big(\theta=1\ \big|\ \mathcal F^{X^s_1}_t\big)\quad\text{a.s.}
--   $$
--
--   This identifies the paper's belief process, defined as a conditional probability, with an explicit continuous process, which is the form used by the two-threshold policy.
--
--   Differences from the source:
--   - encoding: π_t := P(θ = 1 | F^{X^s_1}_t), a conditional probability → the Bayes-formula process posterior, almost surely equal to the conditional expectation of θ = 1{U < y₀} given the filtration; reason: the paper's definition is the conditional probability; this states that the explicit process is a version of it
--   - encoding: the natural filtration satisfying the standard properties → Mathlib's raw natural filtration of X^s_1; reason: conditional expectations given a filtration and given its augmentation agree almost surely
--   - generalization: initial belief π₀ ∈ (0, 1), size S₁ > 0 (for (1)) → y₀ ∈ [0, 1] and S₁ ≥ 0; reason: the endpoints and S₁ = 0 are included; the statement specializes to the paper's range
--   - generalization: one fixed probability space (Ω, F, P) → every probability space satisfying the model's assumptions (Setup); reason: the paper's space is one such space, so the statement specializes to it
--   - encoding: a probability space with Brownian motions, a binary θ with P(θ = 1) = π₀, Itô integrals, the augmented natural filtration of X^s_1 → the Setup structure (θ = 1{U < y₀} from an independent uniform U), the pathwise integration-by-parts discounted integral discInt, Mathlib's raw natural filtration, stopping times in [0, ∞], F_τ-measurable S₂ ≥ 0; reason: the conventions of the mission's definitions; each realizes the paper's object (see the definitions' Formalization Notes and MODERATION_NOTES.md)
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), definition of π_t, p.9 (PDF 9)

import Mathlib
import Definitions.Def_CompInvestBayes_posterior

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

/-- **The posterior belief is the conditional probability of a favorable market**
(SSRN 3408260, definition of `π_t`, p.9, PDF 9): `π_t := P(θ = 1 | F^{X^s_1}_t)`.

For every leader size `S₁ ≥ 0`, prior `y₀ ∈ [0, 1]` and time `t ≥ 0`, the Bayes-formula process
`posterior` is a version of the conditional expectation of `θ = 1{U < y₀}` given the natural
filtration of `X^s_1` at time `t`.

**Formalization Note.** The filtration is Mathlib's raw natural filtration; conditional expectations
given it and given its augmentation agree almost surely. -/
theorem posterior_eq_condExp (p : Params) (hp : p.Standing) {σ : ℝ} (hσ : 0 < σ)
    {Ω : Type*} [MeasurableSpace Ω] (E : Setup Ω) {S1 y0 : ℝ} (hS1 : 0 ≤ S1)
    (hy0 : y0 ∈ Set.Icc (0 : ℝ) 1) (t : ℝ≥0) :
    posterior p σ E S1 y0 t =ᵐ[E.P] E.P[theta E y0 | obsFiltration p σ E S1 y0 t] := by sorry

end CompInvestBayes
