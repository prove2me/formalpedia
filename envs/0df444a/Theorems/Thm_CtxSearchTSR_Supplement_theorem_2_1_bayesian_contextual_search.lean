-- Prove2me | Theorems.Thm_CtxSearchTSR_Supplement_theorem_2_1_bayesian_contextual_search
-- name    : CtxSearchTSR.Supplement.theorem_2_1_bayesian_contextual_search
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:22:56.563055+00:00
-- url     : https://prove2.me/theorems/b682758b-6f60-423c-9669-dc73fa398abd
-- title:
--   Theorem 2.1 — Bayesian contextual search: $\sum_t\mathbb E[\ell_t]\le 24\operatorname{Tr}\sqrt{\Sigma_1}$
-- statement:
--   Let $\pi$ be any prior on the target $z\in\mathbb R^d$ with finite second moments, and let $\Sigma_1=\operatorname{Cov}(\pi)$ be its covariance. Let the contexts be chosen by any adaptive strategy, possibly randomized by an auxiliary randomization $\xi\sim\kappa$ independent of $z$ and of the learner, with $\|x_t\|_2\le 1$ in every round. Then Algorithm 1 (Bayesian Contextual Search) satisfies, for every horizon $T$,
--
--   $$\sum_{t=1}^T\mathbb E[\ell_t]\le 24\operatorname{Tr}\sqrt{\Sigma_1},$$
--
--   where $\ell_t=|x_t^\top z-P_t|$ and the expectation is over the prior, the learner's signs and the randomization of the contexts.
--
--   The bound does not depend on $T$: the total loss of the Bayesian learner is controlled by the prior's spread $\operatorname{Tr}\sqrt{\Sigma_1}$ alone, with no Gaussian, density or bounded-support assumption on the prior.
--
--   **Formalization Note** The expectation is the lower Lebesgue integral of the nonnegative total loss in $[0,\infty]$, compared with $\operatorname{ofReal}(24\operatorname{Tr}\sqrt{\Sigma_1})$.
--
--   Differences from the source:
--   - generalization: every horizon T ≥ 1 (and d ≥ 1 implicit) → every T ∈ ℕ and every d ∈ ℕ; reason: at T = 0 the sum is empty and at d = 0 every context, price and loss is 0, so the bound reads 0 ≤ 24 Tr √Σ₁; it specializes to the paper's T ≥ 1, d ≥ 1
--   - encoding: Σₜ 𝔼[ℓₜ] over the prior, the learner's signs and the randomization of the contexts → the lower Lebesgue integral of Σₜ ℓₜ over ξ ∼ κ, the 2^T sign vectors and z ∼ π, in ℝ≥0∞; reason: losses are nonnegative and Σ𝔼 = 𝔼Σ by linearity; for a measurable strategy the integral is the usual expectation
--   - encoding: "the randomization of the contexts", contexts adaptive to the history F_{t−1} and conditionally independent of z given it (§1.4) → a context is X ξ h, a function of an auxiliary ξ drawn from an arbitrary probability space independent of z and of the signs, and of the observed history h (contexts, prices, feedback, signs); reason: this is the general form of an admissible randomized adaptive strategy; it never sees z or the current sign
--   - encoding: "compute the posterior distribution on z" → the prior conditioned (ProbabilityTheory.cond) on the set of targets consistent with every recorded feedback bit; reason: this is the exact Bayes posterior, because the likelihood of a history is that indicator times factors free of z; histories of prior probability zero carry weight zero
--   - encoding: rounds t = 1, …, T → rounds 0, …, T − 1; reason: Lean indexing; same rounds
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), §2.1, Theorem 2.1, p.8, (7); Algorithm 1 p.8

import Mathlib
import Definitions.Def_CtxSearchTSR_Supplement_Algorithm1

open MeasureTheory Matrix ProbabilityTheory
open scoped ENNReal

namespace CtxSearchTSR.Supplement

/-- **Theorem 2.1 (Bayesian Contextual Search).** Cosson et al., *Contextual Search and Bilateral
Trade with a Trace-Square-Root Potential*, STOC 2027 submission (manuscript sha256 70eeb0d1…),
p.8, (7).

"For any known prior on z ∈ ℝ^d with finite second moment and covariance Σ₁, Algorithm 1
satisfies, for every horizon T ≥ 1, Σ_{t=1}^T E[ℓₜ] ≤ 24 Tr √Σ₁. (7) The expectation is over the
prior and the randomization of the learner and the contexts."

**Formalization Note.** The prior `π` is any Borel probability measure on ℝ^d with square-integrable
coordinates; Σ₁ = `covMat π`. Contexts come from any adaptive strategy `X` with auxiliary
randomization ξ ∼ κ (any probability space), every context in the Euclidean unit ball. The
expectation (`alg1ExpectedTotalLoss`) is over ξ, the learner's uniform signs and z ∼ π, of the
nonnegative total loss, in `ℝ≥0∞`. T = 0 is allowed (the sum is empty). -/
theorem theorem_2_1_bayesian_contextual_search {d : ℕ} (π : Measure (Fin d → ℝ))
    [IsProbabilityMeasure π] (hπ : HasFiniteSecondMoments π)
    {Ξ : Type*} [MeasurableSpace Ξ] (κ : Measure Ξ) [IsProbabilityMeasure κ]
    (X : BayesSearchStrategy d Ξ) (hX : ∀ ξ h, eucNorm (X ξ h) ≤ 1) (T : ℕ) :
    alg1ExpectedTotalLoss π κ X T ≤ ENNReal.ofReal (24 * trSqrt (covMat π)) := by sorry

end CtxSearchTSR.Supplement
