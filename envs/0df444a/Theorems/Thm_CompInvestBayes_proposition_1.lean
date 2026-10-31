-- Prove2me | Theorems.Thm_CompInvestBayes_proposition_1
-- name    : CompInvestBayes.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:14.581931+00:00
-- url     : https://prove2.me/theorems/6c0f00e0-789f-4953-a470-7b8971bc67ec
-- title:
--   Proposition 1 — a two-threshold policy whose value is $C^1$, piecewise $C^2$ and satisfies (13)–(14)
-- statement:
--   Let the standing assumptions hold, $\sigma>0$ and the leader's size $S_1>\mu_L$. There are thresholds $0<\ell<h<1$ such that the value $v(\cdot;S_1)$ of the two-threshold policy $(\ell,h)$ is $C^1$ on $[0,1]$, $C^2$ on each of $[0,\ell]$, $[\ell,h]$, $[h,1]$, and satisfies
--
--   $$
--   g(y)\le v(y;S_1),\quad y\in[0,1],\tag{13}
--   $$
--   $$
--   \tfrac12\,q(S_1)\,y^2(1-y)^2\,v''(y;S_1)\le\lambda\,v(y;S_1),\quad y\in(0,1)\setminus\{\ell,h\}.\tag{14}
--   $$
--
--   These are the hypotheses of the verification argument of Proposition 2(a).
--
--   Differences from the source:
--   - reading: 'C1, piecewise C2' → ContDiffOn ℝ 1 on [0, 1] and ContDiffOn ℝ 2 on [0, ℓ], [ℓ, h], [h, 1]; reason: the pieces of the construction (EC.16) are [0, ℓ*], (ℓ*, h*), [h*, 1]
--   - reading: v''(y; S₁) in (14) → deriv (deriv v) y; reason: off {ℓ, h} the second derivative is the classical one
--   - reading: a two-threshold policy (ℓ*(S₁), h*(S₁), S₂) → thresholds with 0 < ℓ < h < 1; reason: the thresholds are beliefs, and the construction gives ℓ* ∈ (0, c₂λ), h* < 1 (proof of Lemma EC.9, pp.ec22–ec23)
--   - generalization: one fixed probability space (Ω, F, P) → every probability space satisfying the model's assumptions (Setup); reason: the paper's space is one such space, so the statement specializes to it
--   - encoding: a probability space with Brownian motions, a binary θ with P(θ = 1) = π₀, Itô integrals, the augmented natural filtration of X^s_1 → the Setup structure (θ = 1{U < y₀} from an independent uniform U), the pathwise integration-by-parts discounted integral discInt, Mathlib's raw natural filtration, stopping times in [0, ∞], F_τ-measurable S₂ ≥ 0; reason: the conventions of the mission's definitions; each realizes the paper's object (see the definitions' Formalization Notes and MODERATION_NOTES.md)
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), Proposition 1, p.11 (PDF 11)

import Mathlib
import Definitions.Def_CompInvestBayes_IsOptimalThresholds
import Definitions.Def_CompInvestBayes_gImmediate
import Definitions.Def_CompInvestBayes_closedForms

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

/-- **Proposition 1** (SSRN 3408260, p.11, PDF 11). For any leader size `S₁ > µ_L` there is a
two-threshold policy `(ℓ, h, S₂)`, `0 < ℓ < h < 1`, whose value function `v(·; S₁)` (`thrValue`) is
`C¹` on `[0, 1]`, piecewise `C²` (on `[0, ℓ]`, `[ℓ, h]`, `[h, 1]`), and satisfies

(13) `g(y) ≤ v(y; S₁)` for `y ∈ [0, 1]`;

(14) `½ q(S₁) y² (1 − y)² v''(y; S₁) ≤ λ v(y; S₁)` for `y ∈ (0, 1) \ {ℓ, h}`. -/
theorem proposition_1 (p : Params) (hp : p.Standing) {σ : ℝ} (hσ : 0 < σ)
    {Ω : Type*} [MeasurableSpace Ω] (E : Setup Ω) {S1 : ℝ} (hS1 : p.muL < S1) :
    ∃ ℓ h : ℝ, 0 < ℓ ∧ ℓ < h ∧ h < 1 ∧
      ContDiffOn ℝ 1 (thrValue p σ E S1 ℓ h) (Set.Icc 0 1) ∧
      ContDiffOn ℝ 2 (thrValue p σ E S1 ℓ h) (Set.Icc 0 ℓ) ∧
      ContDiffOn ℝ 2 (thrValue p σ E S1 ℓ h) (Set.Icc ℓ h) ∧
      ContDiffOn ℝ 2 (thrValue p σ E S1 ℓ h) (Set.Icc h 1) ∧
      (∀ y ∈ Set.Icc (0 : ℝ) 1, gMax p σ E y ≤ thrValue p σ E S1 ℓ h y) ∧
      (∀ y ∈ Set.Ioo (0 : ℝ) 1, y ≠ ℓ → y ≠ h →
        1 / 2 * q p σ S1 * y ^ 2 * (1 - y) ^ 2 * deriv (deriv (thrValue p σ E S1 ℓ h)) y
          ≤ p.lam * thrValue p σ E S1 ℓ h y) := by sorry

end CompInvestBayes
