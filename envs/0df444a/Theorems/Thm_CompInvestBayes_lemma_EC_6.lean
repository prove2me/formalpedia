-- Prove2me | Theorems.Thm_CompInvestBayes_lemma_EC_6
-- name    : CompInvestBayes.lemma_EC_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:16.925915+00:00
-- url     : https://prove2.me/theorems/423d9a49-ae85-4126-a310-8362bf623c20
-- title:
--   Lemma EC.6 — $\ell^*$ strictly decreases and $h^*$ strictly increases in the signal quality $q(S_1)$
-- statement:
--   Let the standing assumptions hold. Consider two parameter points $(S_1,\sigma)$ and $(S_1',\sigma')$ with $S_1,S_1'>\mu_L$, $\sigma,\sigma'>0$ and everything else equal, such that the signal qualities satisfy $q(S_1;\sigma)<q(S_1';\sigma')$. If $(\ell,h)$ and $(\ell',h')$ are optimal thresholds at the two points, then
--
--   $$
--   \ell'<\ell\qquad\text{and}\qquad h<h'.
--   $$
--
--   A more informative leader widens the follower's waiting region on both sides.
--
--   Differences from the source:
--   - reading: 'ℓ*(S₁) strictly decreases in q(S₁) whereas h*(S₁) strictly increases in q(S₁)' → for two points (S₁, σ), (S₁', σ') with q < q', ℓ' < ℓ and h < h'; reason: the proof takes 'two candidate values q₁ and q₂ for the signal quality'; q varies through S₁ and σ
--   - generalization: the constructed pairs (ℓ*, h*) → every pair of optimal thresholds; reason: the constructed pairs are optimal thresholds (Propositions 1–2(a))
--   - generalization: one fixed probability space (Ω, F, P) → every probability space satisfying the model's assumptions (Setup); reason: the paper's space is one such space, so the statement specializes to it
--   - encoding: a probability space with Brownian motions, a binary θ with P(θ = 1) = π₀, Itô integrals, the augmented natural filtration of X^s_1 → the Setup structure (θ = 1{U < y₀} from an independent uniform U), the pathwise integration-by-parts discounted integral discInt, Mathlib's raw natural filtration, stopping times in [0, ∞], F_τ-measurable S₂ ≥ 0; reason: the conventions of the mission's definitions; each realizes the paper's object (see the definitions' Formalization Notes and MODERATION_NOTES.md)
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), Lemma EC.6, p.ec7 (PDF 39)

import Mathlib
import Definitions.Def_CompInvestBayes_IsOptimalThresholds
import Definitions.Def_CompInvestBayes_closedForms

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

/-- **Lemma EC.6** (SSRN 3408260, p.ec7, PDF 39). For leader sizes `S₁ > µ_L`, `ℓ*(S₁)` strictly
decreases in the signal quality `q(S₁)` whereas `h*(S₁)` strictly increases in `q(S₁)`.

Stated for two parameter points `(S₁, σ)` and `(S₁', σ')` with `S₁, S₁' > µ_L` (everything else
fixed): if `q(S₁; σ) < q(S₁'; σ')` and `(ℓ, h)`, `(ℓ', h')` are optimal thresholds at the two points,
then `ℓ' < ℓ` and `h < h'`. -/
theorem lemma_EC_6 (p : Params) (hp : p.Standing) {σ σ' : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ')
    {Ω : Type*} [MeasurableSpace Ω] (E : Setup Ω) {S1 S1' ℓ h ℓ' h' : ℝ}
    (hS1 : p.muL < S1) (hS1' : p.muL < S1') (hq : q p σ S1 < q p σ' S1')
    (hopt : IsOptimalThresholds p σ E S1 ℓ h) (hopt' : IsOptimalThresholds p σ' E S1' ℓ' h') :
    ℓ' < ℓ ∧ h < h' := by sorry

end CompInvestBayes
