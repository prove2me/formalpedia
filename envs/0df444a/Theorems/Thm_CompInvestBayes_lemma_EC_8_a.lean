-- Prove2me | Theorems.Thm_CompInvestBayes_lemma_EC_8_a
-- name    : CompInvestBayes.lemma_EC_8_a
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:38.962248+00:00
-- url     : https://prove2.me/theorems/1fe3be3f-dd86-4fc6-b2f4-4cc1833fd0d8
-- title:
--   Lemma EC.8(a) — $H_1>H_0$ on $\mathcal R_1$
-- statement:
--   Let the standing assumptions hold, $\sigma>0$, $S_1>\mu_L$, and $(\ell,h)$ optimal thresholds. For every $y_0\in(\ell,h)$,
--
--   $$
--   H_1(S_1,y_0)>H_0(S_1,y_0).
--   $$
--
--   Delaying the follower's entry is strictly profitable for the leader: before entry it serves the whole market.
--
--   Differences from the source:
--   - generalization: R₁ = (µ_L, ∞) × (ℓ*(S₁), h*(S₁)) → (µ_L, ∞) × (ℓ, h) for every pair (ℓ, h) of optimal thresholds; reason: the paper's pair is optimal (Propositions 1–2(a))
--   - generalization: one fixed probability space (Ω, F, P) → every probability space satisfying the model's assumptions (Setup); reason: the paper's space is one such space, so the statement specializes to it
--   - encoding: a probability space with Brownian motions, a binary θ with P(θ = 1) = π₀, Itô integrals, the augmented natural filtration of X^s_1 → the Setup structure (θ = 1{U < y₀} from an independent uniform U), the pathwise integration-by-parts discounted integral discInt, Mathlib's raw natural filtration, stopping times in [0, ∞], F_τ-measurable S₂ ≥ 0; reason: the conventions of the mission's definitions; each realizes the paper's object (see the definitions' Formalization Notes and MODERATION_NOTES.md)
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), Lemma EC.8(a), p.ec21 (PDF 53)

import Mathlib
import Definitions.Def_CompInvestBayes_IsOptimalThresholds
import Definitions.Def_CompInvestBayes_closedForms

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

/-- **Lemma EC.8(a)** (SSRN 3408260, p.ec21, PDF 53). `H₁(S₁, y₀) > H₀(S₁, y₀)` for
`(S₁, y₀) ∈ R₁ = (µ_L, ∞) × (ℓ*(S₁), h*(S₁))`, for every pair `(ℓ, h)` of optimal thresholds. -/
theorem lemma_EC_8_a (p : Params) (hp : p.Standing) {σ : ℝ} (hσ : 0 < σ)
    {Ω : Type*} [MeasurableSpace Ω] (E : Setup Ω) {S1 ℓ h y0 : ℝ} (hS1 : p.muL < S1)
    (hopt : IsOptimalThresholds p σ E S1 ℓ h) (hy0 : y0 ∈ Set.Ioo ℓ h) :
    H0 p S1 y0 < H1 p σ S1 ℓ h y0 := by sorry

end CompInvestBayes
