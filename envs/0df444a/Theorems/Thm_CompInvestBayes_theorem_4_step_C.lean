-- Prove2me | Theorems.Thm_CompInvestBayes_theorem_4_step_C
-- name    : CompInvestBayes.theorem_4_step_C
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:29.503586+00:00
-- url     : https://prove2.me/theorems/a6d9ef3b-9ab6-4d27-9521-afc20d0307a7
-- title:
--   Proof of Theorem 4, Step C (corrected: requires $c_1\le c_2$) — no leader size $S_1\le\mu_L$ is optimal at $y_0=c_2\lambda$
-- statement:
--   Let the standing assumptions hold, $\mu_L<\mu_{1,H}$, $c_1\le c_2$ and $\sigma>0$. For every selection of follower best responses and every leader size $S_1\in[0,\mu_L]$, the leader's profit at the prior $y_0=c_2\lambda$ is strictly below its equilibrium value:
--
--   $$
--   H(S_1,c_2\lambda)<V_1(c_2\lambda).
--   $$
--
--   Hence the leader's equilibrium size $\tilde S_1(c_2\lambda)$ exceeds $\mu_L$, and the follower waits at $y_0=c_2\lambda$ in equilibrium.
--
--   Without $c_1\le c_2$ the claim fails: with $\lambda=0.1$, $c_1=5$, $c_2=1$, $\mu_{1,L}=0.5$, $\mu_{1,H}=2$, $\mu_{2,L}=1$, $\mu_{2,H}=2$ (all standing assumptions and (30) hold), $S_1=\mu_{1,L}$ gives $H=2.5$ near $c_2\lambda=0.1$, while every $S_1>\mu_L$ has $H_0(S_1,y_0)\le-1$ and an extra pre-entry profit that vanishes as $\sigma\to\infty$ (Proposition 3(a)); so for large $\sigma$ the leader's optimal size is $\mu_{1,L}\le\mu_L$, as the paper's own Theorem 2 predicts for $y_0\le c_1\lambda$.
--
--   Differences from the source:
--   - correction: S̃₁(c₂λ) > µ_L when µ_L < µ_{1,H} → adds the hypothesis c₁ ≤ c₂; reason: counterexample: λ = 0.1, c₁ = 5, c₂ = 1, µ_{1,L} = 0.5, µ_{1,H} = 2, µ_{2,L} = 1, µ_{2,H} = 2 satisfies every assumption; for large σ the leader's optimal size at c₂λ is µ_{1,L} ≤ µ_L (paper.md; consistent with Theorem 2)
--   - reading: S̃₁(c₂λ) > µ_L, for the equilibrium size S̃₁ → every S₁ ∈ [0, µ_L] has H(S₁, c₂λ) < V₁(c₂λ); reason: this is 'no maximizer lies in [0, µ_L]' and makes no claim that the maximum is attained
--   - generalization: the equilibrium follower policy → every best-response selection of the follower; reason: the paper's policy is one selection
--   - encoding: max_{S₁≥0} in V₁ → sSup over S₁ ≥ 0; reason: Lean convention; payoffs are bounded above by µ_H/λ
--   - generalization: one fixed probability space (Ω, F, P) → every probability space satisfying the model's assumptions (Setup); reason: the paper's space is one such space, so the statement specializes to it
--   - encoding: a probability space with Brownian motions, a binary θ with P(θ = 1) = π₀, Itô integrals, the augmented natural filtration of X^s_1 → the Setup structure (θ = 1{U < y₀} from an independent uniform U), the pathwise integration-by-parts discounted integral discInt, Mathlib's raw natural filtration, stopping times in [0, ∞], F_τ-measurable S₂ ≥ 0; reason: the conventions of the mission's definitions; each realizes the paper's object (see the definitions' Formalization Notes and MODERATION_NOTES.md)
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), proof of Theorem 4, Step C, p.ec26 (PDF 58)

import Mathlib
import Definitions.Def_CompInvestBayes_V1

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

/-- **Proof of Theorem 4, Step C** (SSRN 3408260, p.ec26, PDF 58), corrected: "We already know
from the proof of Theorem 3 that S̃₁(c₂λ) > µ_L when µ_L < µ_{1,H}", under the added hypothesis
`c₁ ≤ c₂`.

For every best-response selection of the follower and every leader size `S₁ ∈ [0, µ_L]`, the
leader's profit at the prior `y₀ = c₂λ` is strictly below its equilibrium value `V₁(c₂λ)`: no size
`S₁ ≤ µ_L` is optimal for the leader at `y₀ = c₂λ`. -/
theorem theorem_4_step_C (p : Params) (hp : p.Standing) (hμ : p.muL < p.mu1H)
    (hc : p.c1 ≤ p.c2) {σ : ℝ} (hσ : 0 < σ) {Ω : Type*} [MeasurableSpace Ω] (E : Setup Ω)
    (br : (S1 y0 : ℝ) → FollowerStrategy p σ E S1 y0) (hbr : IsBestResponseSelection br)
    {S1 : ℝ} (hS1 : 0 ≤ S1) (hS1' : S1 ≤ p.muL) :
    leaderPayoff p σ E S1 (p.c2 * p.lam) (br S1 (p.c2 * p.lam)).τ
      < V1 p σ E br (p.c2 * p.lam) := by sorry

end CompInvestBayes
