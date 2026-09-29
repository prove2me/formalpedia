-- Prove2me | Theorems.Thm_FamousTheorems_strong_law_ae
-- name    : FamousTheorems.strong_law_ae
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T23:06:14.367204+00:00
-- url     : https://prove2.me/theorems/07c6d68b-d4ca-4c25-af01-d81f3c1bc2b8
-- title:
--   The strong law of large numbers
-- statement:
--   **The strong law of large numbers** (Etemadi's form).
--
--   Let $X_0, X_1, \dots$ be pairwise independent, identically distributed, integrable random variables
--   taking values in a Banach space. Then almost surely
--   $$\frac{1}{n}\sum_{i<n} X_i \;\longrightarrow\; \mathbb{E}[X_0].$$
--
--   "Strong" distinguishes almost-sure convergence from the weak law's convergence in probability: the
--   weak law says that for each large $n$ the average is probably close to the mean, while the strong law
--   says that along almost every single realisation the averages settle down and stay close. This is what
--   justifies reading an empirical average as an estimate of an expectation, and it is the theorem behind
--   Monte Carlo integration.
--
--   Two hypotheses are weaker than one might expect. Only *pairwise* independence is needed — this
--   sharpening is due to Etemadi (1981) and is genuinely surprising, since most limit theorems require
--   full independence. And only integrability is assumed, no variance; Kolmogorov proved integrability
--   is also necessary, since without it the averages almost surely fail to converge.
--
--   Borel proved the case of coin flips (the normal number theorem) in 1909; Kolmogorov gave the general
--   independent case in 1933.
--
--   **Formalization note.** `⟂ᵢ[μ]` is independence of two random variables, applied pairwise along `X`;
--   `μ[X 0]` is the Bochner integral. The result is Mathlib's `ProbabilityTheory.strong_law_ae`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology

theorem strong_law_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (X : ℕ → Ω → E) (hint : Integrable (X 0) μ)
    (hindep : Pairwise (Function.onFun (· ⟂ᵢ[μ] ·) X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω)) atTop (𝓝 μ[X 0]) := by sorry

end FamousTheorems
