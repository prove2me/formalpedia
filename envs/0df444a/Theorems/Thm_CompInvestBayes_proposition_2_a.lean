-- Prove2me | Theorems.Thm_CompInvestBayes_proposition_2_a
-- name    : CompInvestBayes.proposition_2_a
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:32.516244+00:00
-- url     : https://prove2.me/theorems/7c75d25f-f409-4704-9b56-77beae959a3d
-- title:
--   Proposition 2(a) — for $S_1>\mu_L$ the two-threshold policy of Proposition 1 is optimal
-- statement:
--   Let the standing assumptions hold, $\sigma>0$ and $S_1>\mu_L$. Let $0<\ell<h<1$ be thresholds whose policy value $v(\cdot;S_1)$ is $C^1$ on $[0,1]$, $C^2$ on $[0,\ell]$, $[\ell,h]$, $[h,1]$, and satisfies (13) and (14) of Proposition 1. Then $(\ell,h)$ are optimal thresholds: for every prior $y_0\in[0,1]$ it is optimal for the follower to wait while $\pi_t\in(\ell,h)$ and to invest, at the first time $\pi_t\notin(\ell,h)$, the size
--
--   $$
--   S^*_2=\begin{cases}\mu_{2,L} & \pi_\tau\in[0,\ell],\\ \mu_{2,H} & \pi_\tau\in[h,1].\end{cases}
--   $$
--
--   The policy is a feasible strategy (its time is a stopping time and its size is known at entry) and no feasible strategy does better.
--
--   Differences from the source:
--   - generalization: 'the two-threshold policy analyzed in Proposition 1' → every thresholds 0 < ℓ < h < 1 whose policy value satisfies the conclusions of Proposition 1; reason: the verification argument (EC.20)–(EC.23) uses only these properties; the constructed pair is one such pair
--   - reading: 'an optimal policy for the follower ... wait whenever π_t ∈ (ℓ*, h*) ... invest S*₂' → IsOptimalThresholds: for every y₀ ∈ [0, 1] the policy is a feasible follower strategy and a best response; reason: optimality is maximality of (7) over all feasible strategies, for every prior
--   - generalization: one fixed probability space (Ω, F, P) → every probability space satisfying the model's assumptions (Setup); reason: the paper's space is one such space, so the statement specializes to it
--   - encoding: a probability space with Brownian motions, a binary θ with P(θ = 1) = π₀, Itô integrals, the augmented natural filtration of X^s_1 → the Setup structure (θ = 1{U < y₀} from an independent uniform U), the pathwise integration-by-parts discounted integral discInt, Mathlib's raw natural filtration, stopping times in [0, ∞], F_τ-measurable S₂ ≥ 0; reason: the conventions of the mission's definitions; each realizes the paper's object (see the definitions' Formalization Notes and MODERATION_NOTES.md)
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), Proposition 2(a), p.12 (PDF 12)

import Mathlib
import Definitions.Def_CompInvestBayes_IsOptimalThresholds
import Definitions.Def_CompInvestBayes_gImmediate
import Definitions.Def_CompInvestBayes_closedForms

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

/-- **Proposition 2(a)** (SSRN 3408260, p.12, PDF 12). For any leader size `S₁ > µ_L`, the
two-threshold policy analyzed in Proposition 1 is optimal for the follower: if `0 < ℓ < h < 1` and
the value function `v(·; S₁)` of the policy `(ℓ, h)` is `C¹`, piecewise `C²` and satisfies (13) and
(14), then for every prior `y₀ ∈ [0, 1]` the policy (wait while `π_t ∈ (ℓ, h)`; invest
`S*₂ = µ_{2,L}` if `π_τ ∈ [0, ℓ]`, `µ_{2,H}` if `π_τ ∈ [h, 1]`) is a feasible follower strategy and is
optimal. -/
theorem proposition_2_a (p : Params) (hp : p.Standing) {σ : ℝ} (hσ : 0 < σ)
    {Ω : Type*} [MeasurableSpace Ω] (E : Setup Ω) {S1 ℓ h : ℝ} (hS1 : p.muL < S1)
    (hℓ : 0 < ℓ) (hℓh : ℓ < h) (hh : h < 1)
    (hC1 : ContDiffOn ℝ 1 (thrValue p σ E S1 ℓ h) (Set.Icc 0 1))
    (hC2a : ContDiffOn ℝ 2 (thrValue p σ E S1 ℓ h) (Set.Icc 0 ℓ))
    (hC2b : ContDiffOn ℝ 2 (thrValue p σ E S1 ℓ h) (Set.Icc ℓ h))
    (hC2c : ContDiffOn ℝ 2 (thrValue p σ E S1 ℓ h) (Set.Icc h 1))
    (h13 : ∀ y ∈ Set.Icc (0 : ℝ) 1, gMax p σ E y ≤ thrValue p σ E S1 ℓ h y)
    (h14 : ∀ y ∈ Set.Ioo (0 : ℝ) 1, y ≠ ℓ → y ≠ h →
      1 / 2 * q p σ S1 * y ^ 2 * (1 - y) ^ 2 * deriv (deriv (thrValue p σ E S1 ℓ h)) y
        ≤ p.lam * thrValue p σ E S1 ℓ h y) :
    IsOptimalThresholds p σ E S1 ℓ h := by sorry

end CompInvestBayes
