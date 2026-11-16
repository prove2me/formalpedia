-- Prove2me | Theorems.Thm_CtxSearchTSR_Supplement_theorem_3_2_bayesian_bilateral_trade
-- name    : CtxSearchTSR.Supplement.theorem_3_2_bayesian_bilateral_trade
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:23:43.982213+00:00
-- url     : https://prove2.me/theorems/0082dde0-b174-4959-8efe-81693bea638e
-- title:
--   Theorem 3.2 — Bayesian bilateral trade: $\sum_t\mathbb E[\ell_t]\le 2^{11}\Psi_{\mathrm{tr}}(\pi)$
-- statement:
--   Let $\pi$ be any joint prior on the seller–buyer pair $(s,b)\in\mathbb R^d\times\mathbb R^d$ with finite second moments ($s$ and $b$ may be dependent). Let $\rho$ be any price rule satisfying (17) of Lemma 3.1: for every joint law $\mu$ of a pair $(S,B)$ of square-integrable reals, $L_\mu(\rho(\mu))\le 2^{11}D_\mu(\rho(\mu))$. Let the contexts be chosen by any adaptive strategy, possibly randomized by an auxiliary $\xi\sim\kappa$ independent of $(s,b)$, with $\|x_t\|_2\le1$. Then Algorithm 3 with this rule satisfies, at every horizon $T$,
--
--   $$\sum_{t=1}^T\mathbb E[\ell_t]\le 2^{11}\,\Psi_{\mathrm{tr}}(\pi),\qquad \Psi_{\mathrm{tr}}(\pi)=\operatorname{Tr}\sqrt{\operatorname{Cov}(s)}+\operatorname{Tr}\sqrt{\operatorname{Cov}(b)},$$
--
--   where $\ell_t=(x_t^\top(b-s))_+(1-Y_t)$ is the lost gain from trade and the expectation is over $\xi$ and $(s,b)\sim\pi$.
--
--   The guarantee is uniform in the horizon. If $\pi$ is supported on the product of unit balls, $\Psi_{\mathrm{tr}}(\pi)\le 2\sqrt d$.
--
--   **Formalization Note** The paper specifies Algorithm 3 as "apply Lemma 3.1 under $\pi_t$ … and post the resulting price", so the theorem is stated for every price rule with property (17); Lemma 3.1 is what makes such rules exist. The expectation is a lower Lebesgue integral in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: Algorithm 3 "applies Lemma 3.1 under πₜ … and posts the resulting price" (a price "chosen as a function of the joint distribution") → every price rule ρ on joint laws of (S, B) that satisfies (17) for every probability measure on ℝ² with square-integrable coordinates; reason: the paper defines the algorithm only through the lemma's property, and every price the lemma supplies is such a rule
--   - generalization: every horizon (T ≥ 1) and d ≥ 1 implicit → every T ∈ ℕ and every d ∈ ℕ; reason: at T = 0 the sum is empty and at d = 0 every loss is 0; it specializes to the paper's statement
--   - encoding: Σₜ 𝔼[ℓₜ] → the lower Lebesgue integral of Σₜ ℓₜ over ξ ∼ κ and (s, b) ∼ π, in ℝ≥0∞; reason: losses are nonnegative, Σ𝔼 = 𝔼Σ, and the integral is the usual expectation for a measurable strategy
--   - encoding: adaptive contexts conditionally independent of the pair given the history (§1.4) → a context is X ξ h, a function of an auxiliary ξ independent of (s, b) and of the observed history (contexts, prices, trade bits); reason: general form of an admissible randomized adaptive strategy
--   - encoding: "condition the joint posterior on this bit and the posted offer" → the prior conditioned on the pairs consistent with every recorded trade bit; reason: the exact Bayes posterior, since each bit is a deterministic function of the pair given the price
--   - encoding: ℓₜ = (xₜᵀ(b − s))₊(1 − Yₜ) → (xₜᵀb − xₜᵀs)₊(1 − Yₜ) with the trade bit as a Boolean; reason: linearity of the dot product; same values
--   - encoding: rounds t = 1, …, T → rounds 0, …, T − 1; reason: Lean indexing; same rounds
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), §3.1, Theorem 3.2, p.13, (18); Algorithm 3 p.13; Lemma 3.1 (17) p.12; (14) p.11

import Mathlib
import Definitions.Def_CtxSearchTSR_Protocol
import Definitions.Def_CtxSearchTSR_Supplement_Algorithm3

open MeasureTheory Matrix ProbabilityTheory
open scoped ENNReal

namespace CtxSearchTSR.Supplement

/-- **Theorem 3.2 (Bayesian Bilateral Trade).** Cosson et al., *Contextual Search and Bilateral
Trade with a Trace-Square-Root Potential*, STOC 2027 submission (manuscript sha256 70eeb0d1…),
p.13, (18).

"For every known joint prior π with finite second moments, Algorithm 3 satisfies the following
bound at every horizon: Σ_{t=1}^T E[ℓₜ] ≤ 2¹¹ Ψtr(π). (18)"

**Formalization Note.** The joint prior `π` of (s, b) is any Borel probability measure on
ℝ^d × ℝ^d whose 2d coordinates are square-integrable (s and b may be dependent). Algorithm 3 posts
`ρ` of the current posterior law of (xᵀs, xᵀb), for any price rule `ρ` with property (17) of
Lemma 3.1 (`PriceRule17`), which is how the paper's algorithm is specified ("apply Lemma 3.1").
Contexts come from any adaptive strategy with auxiliary randomization ξ ∼ κ, in the Euclidean unit
ball. The expectation is over ξ and (s, b) ∼ π, in `ℝ≥0∞`. Ψtr(π) = Tr √Cov(s) + Tr √Cov(b). -/
theorem theorem_3_2_bayesian_bilateral_trade {d : ℕ}
    (π : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsProbabilityMeasure π]
    (hπ : ∀ i : Fin d, MemLp (fun w : (Fin d → ℝ) × (Fin d → ℝ) => w.1 i) 2 π ∧
      MemLp (fun w : (Fin d → ℝ) × (Fin d → ℝ) => w.2 i) 2 π)
    (ρ : Measure (ℝ × ℝ) → ℝ) (hρ : PriceRule17 ρ)
    {Ξ : Type*} [MeasurableSpace Ξ] (κ : Measure Ξ) [IsProbabilityMeasure κ]
    (X : BayesTradeStrategy d Ξ) (hX : ∀ ξ h, eucNorm (X ξ h) ≤ 1) (T : ℕ) :
    alg3ExpectedTotalLoss π ρ κ X T ≤ ENNReal.ofReal (2 ^ 11 * psiTr π) := by sorry

end CtxSearchTSR.Supplement
