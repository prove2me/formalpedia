-- Prove2me | Theorems.Thm_CompInvestBayes_theorem_1
-- name    : CompInvestBayes.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:09:04.951544+00:00
-- url     : https://prove2.me/theorems/a4e19bef-4438-4128-bec6-216b89476d71
-- title:
--   Theorem 1 — the leader's profit is $H_0$ on $\mathcal R_0$ and $H_1$ on $\mathcal R_1$
-- statement:
--   Let the standing assumptions hold and $\sigma>0$. Let $S_1\ge0$, $y_0\in[0,1]$ and let $s$ be any best response of the follower at $(S_1,y_0)$, entering at $\tau$. Write $H(S_1,y_0)$ for the leader's profit (15) against $s$. Then
--
--   1. if $S_1\le\mu_L$: $H(S_1,y_0)=H_0(S_1,y_0)$;
--   2. if $S_1>\mu_L$ and $(\ell,h)$ are optimal thresholds: $H(S_1,y_0)=H_0(S_1,y_0)$ when $y_0\in[0,\ell]\cup[h,1]$, and $H(S_1,y_0)=H_1(S_1,y_0)$ when $y_0\in(\ell,h)$,
--
--   where $H_0$ is (22) and $H_1$ is (23)–(25), i.e. $H=H_0$ on $\mathcal R_0=[0,\mu_L]\times[0,1]\cup(\mu_L,\infty)\times([0,\ell^*]\cup[h^*,1])$ and $H=H_1$ on $\mathcal R_1=(\mu_L,\infty)\times(\ell^*,h^*)$.
--
--   This reduces the leader's problem to the closed-form optimization (26).
--
--   Differences from the source:
--   - generalization: H(S₁, y₀) 'subject to the follower's optimal policy ... in Proposition 2' → the leader's profit against every best response s of the follower at (S₁, y₀); reason: the leader's profit depends on s only through τ, and optimal entry times agree a.s.; the paper's policy is one best response
--   - generalization: R₀, R₁ defined with ℓ*(S₁), h*(S₁) → every pair (ℓ, h) of optimal thresholds; reason: the paper's pair is optimal (Propositions 1–2(a))
--   - generalization: one fixed probability space (Ω, F, P) → every probability space satisfying the model's assumptions (Setup); reason: the paper's space is one such space, so the statement specializes to it
--   - encoding: a probability space with Brownian motions, a binary θ with P(θ = 1) = π₀, Itô integrals, the augmented natural filtration of X^s_1 → the Setup structure (θ = 1{U < y₀} from an independent uniform U), the pathwise integration-by-parts discounted integral discInt, Mathlib's raw natural filtration, stopping times in [0, ∞], F_τ-measurable S₂ ≥ 0; reason: the conventions of the mission's definitions; each realizes the paper's object (see the definitions' Formalization Notes and MODERATION_NOTES.md)
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), Theorem 1, eqs. (21)–(25), pp.13–14 (PDF 13–14)

import Mathlib
import Definitions.Def_CompInvestBayes_V1
import Definitions.Def_CompInvestBayes_IsOptimalThresholds
import Definitions.Def_CompInvestBayes_closedForms

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

/-- **Theorem 1** (SSRN 3408260, pp.13–14, PDF 13–14). The leader's profit `H(S₁, y₀)` (15),
computed against the follower's optimal policy, satisfies `H = H₀` on `R₀` and `H = H₁` on `R₁`, where
`R₀ = [0, µ_L] × [0, 1] ∪ (µ_L, ∞) × ([0, ℓ*(S₁)] ∪ [h*(S₁), 1])` and
`R₁ = (µ_L, ∞) × (ℓ*(S₁), h*(S₁))`, and `H₀` (22), `H₁` (23)–(25) are the closed forms.

Stated for every optimal follower strategy `s` at `(S₁, y₀)` and, when `S₁ > µ_L`, for every pair of
optimal thresholds `(ℓ, h)`. -/
theorem theorem_1 (p : Params) (hp : p.Standing) {σ : ℝ} (hσ : 0 < σ)
    {Ω : Type*} [MeasurableSpace Ω] (E : Setup Ω) {S1 y0 : ℝ} (hS1 : 0 ≤ S1)
    (hy0 : y0 ∈ Set.Icc (0 : ℝ) 1) (s : FollowerStrategy p σ E S1 y0)
    (hs : IsFollowerOptimal s) :
    (S1 ≤ p.muL → leaderPayoff p σ E S1 y0 s.τ = H0 p S1 y0) ∧
      (p.muL < S1 → ∀ ℓ h : ℝ, IsOptimalThresholds p σ E S1 ℓ h →
        ((y0 ≤ ℓ ∨ h ≤ y0) → leaderPayoff p σ E S1 y0 s.τ = H0 p S1 y0) ∧
        (ℓ < y0 → y0 < h → leaderPayoff p σ E S1 y0 s.τ = H1 p σ S1 ℓ h y0)) := by sorry

end CompInvestBayes
