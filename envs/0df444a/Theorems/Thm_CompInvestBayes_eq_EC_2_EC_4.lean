-- Prove2me | Theorems.Thm_CompInvestBayes_eq_EC_2_EC_4
-- name    : CompInvestBayes.eq_EC_2_EC_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:44.852512+00:00
-- url     : https://prove2.me/theorems/e415d8c3-e600-446b-b104-fceb50543a32
-- title:
--   (EC.2)–(EC.4): the follower's immediate-investment profit $g(y)$ in closed form
-- statement:
--   Let the standing assumptions hold and $\sigma>0$. For every belief $y\in[0,1]$:
--
--   1. (EC.2) for every size $S_2\ge0$,
--   $$
--   g(y,S_2)=\frac{y\min(S_2,\mu_{2,H})+(1-y)\min(S_2,\mu_{2,L})}{\lambda}-c_2S_2;
--   $$
--   2. (EC.3) the size $S^*_2(y)$ ($\mu_{2,L}$ for $y\le c_2\lambda$, $\mu_{2,H}$ for $y>c_2\lambda$) attains $g(y)=\max_{S_2\ge0}g(y,S_2)$, and for $y\ne c_2\lambda$ it is the unique maximizer;
--   3. (EC.4)
--   $$
--   g(y)=\begin{cases}\big(\tfrac1\lambda-c_2\big)\mu_{2,L}, & 0\le y\le c_2\lambda,\\[2pt] \tfrac1\lambda(\mu_{2,H}-\mu_{2,L})\,y+\tfrac1\lambda\mu_{2,L}-c_2\mu_{2,H}, & c_2\lambda<y\le1.\end{cases}
--   $$
--
--   This is the payoff of stopping in the follower's optimal stopping problem: it is increasing, piecewise linear, convex and positive, with a kink at $c_2\lambda$.
--
--   Differences from the source:
--   - generalization: (EC.2): equality of the two maxima over S₂ ≥ 0 → equality of g(y, S₂) with the closed form for every S₂ ≥ 0; reason: the pointwise identity implies the equality of the maxima
--   - reading: 'the maximizer S*₂ in (EC.2) ... is' (EC.3) → S*₂ attains the maximum, and is the unique maximizer for y ≠ c₂λ; reason: at y = c₂λ every S₂ ∈ [µ_{2,L}, µ_{2,H}] maximizes (the slope y/λ − c₂ vanishes), so 'the' maximizer is unique only off c₂λ
--   - encoding: max_{S₂≥0} → sSup over S₂ ≥ 0, with attainment stated; reason: Lean convention; attainment is part of the statement
--   - generalization: one fixed probability space (Ω, F, P) → every probability space satisfying the model's assumptions (Setup); reason: the paper's space is one such space, so the statement specializes to it
--   - encoding: a probability space with Brownian motions, a binary θ with P(θ = 1) = π₀, Itô integrals, the augmented natural filtration of X^s_1 → the Setup structure (θ = 1{U < y₀} from an independent uniform U), the pathwise integration-by-parts discounted integral discInt, Mathlib's raw natural filtration, stopping times in [0, ∞], F_τ-measurable S₂ ≥ 0; reason: the conventions of the mission's definitions; each realizes the paper's object (see the definitions' Formalization Notes and MODERATION_NOTES.md)
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), proof of Lemma EC.1(a), (EC.2)–(EC.4), p.ec2 (PDF 34)

import Mathlib
import Definitions.Def_CompInvestBayes_gImmediate

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

/-- **The follower's immediate-investment profit in closed form** (SSRN 3408260, proof of
Lemma EC.1(a), (EC.2)–(EC.4), p.ec2, PDF 34).

For every belief `y ∈ [0, 1]`:
1. (EC.2) for every size `S₂ ≥ 0`,
   `g(y, S₂) = [y min(S₂, µ_{2,H}) + (1 − y) min(S₂, µ_{2,L})]/λ − c₂S₂`;
2. (EC.3) the size `S*₂ = µ_{2,L}` (`y ≤ c₂λ`), `µ_{2,H}` (`y > c₂λ`) attains `g(y) = max_{S₂≥0} g(y, S₂)`,
   and for `y ≠ c₂λ` it is the unique maximizer over `S₂ ≥ 0` (at `y = c₂λ` every
   `S₂ ∈ [µ_{2,L}, µ_{2,H}]` maximizes);
3. (EC.4) `g(y) = (1/λ − c₂) µ_{2,L}` for `0 ≤ y ≤ c₂λ` and
   `g(y) = (µ_{2,H} − µ_{2,L}) y/λ + µ_{2,L}/λ − c₂µ_{2,H}` for `c₂λ < y ≤ 1`. -/
theorem eq_EC_2_EC_4 (p : Params) (hp : p.Standing) {σ : ℝ} (hσ : 0 < σ)
    {Ω : Type*} [MeasurableSpace Ω] (E : Setup Ω) {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (∀ S2 : ℝ, 0 ≤ S2 →
        gImm p σ E y S2 = (y * min S2 p.mu2H + (1 - y) * min S2 p.mu2L) / p.lam - p.c2 * S2) ∧
      gImm p σ E y (S2star p y) = gMax p σ E y ∧
      (y ≠ p.c2 * p.lam → ∀ S2 : ℝ, 0 ≤ S2 → S2 ≠ S2star p y →
        gImm p σ E y S2 < gImm p σ E y (S2star p y)) ∧
      gMax p σ E y =
        if y ≤ p.c2 * p.lam then (1 / p.lam - p.c2) * p.mu2L
        else 1 / p.lam * (p.mu2H - p.mu2L) * y + 1 / p.lam * p.mu2L - p.c2 * p.mu2H := by sorry

end CompInvestBayes
