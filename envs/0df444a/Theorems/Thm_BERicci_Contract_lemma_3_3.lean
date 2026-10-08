-- Prove2me | Theorems.Thm_BERicci_Contract_lemma_3_3
-- name    : BERicci.Contract.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:30.562686+00:00
-- url     : https://prove2.me/theorems/25db1f1a-64f9-4cd0-9cf7-3dc55b6718cb
-- title:
--   Lemma 3.3, p. 29 — limsup of ∫ f_n dμ_n under weak convergence and a sequential upper bound
-- statement:
--   Let $(X,\mathsf d)$ be a metric space with its Borel σ-algebra. Let $\mu_n,\mu$ be Borel probability measures with $\mu_n\to\mu$ weakly, i.e. $\int g\,d\mu_n\to\int g\,d\mu$ for every bounded continuous $g$. Let $f_n:X\to\mathbb R$ be Borel functions with $\sup_{n,x}|f_n(x)|<\infty$, and let $f$ be a Borel function such that
--   $$\limsup_{n\to\infty}f_n(x_n)\le f(x)\qquad\text{whenever }x_n\to x.$$
--   Then
--   $$\limsup_{n\to\infty}\int_Xf_n\,d\mu_n\le\int_Xf\,d\mu.$$
--
--   This is a Fatou-type lemma for varying measures; in the paper it is applied with $\mu_h=\mathsf H_t\delta_{\gamma_{s+h}}$ and difference quotients of the Hopf–Lax map in the proof of Lemma 3.4.
--
--   **Formalization Note** The functions $f_n$ are equibounded by some $M$, and taking $x_n=x$ in the hypothesis gives $f\ge-M$; so if $f$ is not $\mu$-integrable then $\int f\,d\mu=+\infty$ and the claim is trivial. The Lean statement therefore assumes `Integrable f μ`, which only removes that trivial case (Lean's Bochner integral would return $0$ there). Completeness and separability of $X$ are not needed and are dropped.
-- source:
--   arXiv:1209.5786v4, Lemma 3.3, p. 29

import Mathlib
import Definitions.Def_BERicci_Contract_Bounds

namespace BERicci.Contract

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- **Lemma 3.3**, p. 29: if `μ_n → μ` weakly in `𝒫(X)` and the equibounded Borel functions `f_n`
satisfy `limsup_n f_n(x_n) ≤ f(x)` whenever `x_n → x`, for a Borel `f`, then
`limsup_n ∫ f_n dμ_n ≤ ∫ f dμ`. (`f ≥ −M` follows from the hypotheses, so a non-integrable `f` has
`∫ f dμ = +∞` and the claim is trivial there; `Integrable f μ` only excludes that case.) -/
theorem lemma_3_3
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μs : ℕ → Measure X) (μ : Measure X)
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) (hμ : IsProbabilityMeasure μ)
    (hweak : ∀ g : BoundedContinuousFunction X ℝ,
      Tendsto (fun n => ∫ x, g x ∂(μs n)) atTop (𝓝 (∫ x, g x ∂μ)))
    (fs : ℕ → X → ℝ) (hfs : ∀ n, Measurable (fs n)) (hbdd : ∃ M : ℝ, ∀ n x, |fs n x| ≤ M)
    (f : X → ℝ) (hf : Measurable f)
    (hlim : ∀ (xs : ℕ → X) (x : X), Tendsto xs atTop (𝓝 x) →
      limsup (fun n => fs n (xs n)) atTop ≤ f x)
    (hfi : Integrable f μ) :
    limsup (fun n => ∫ x, fs n x ∂(μs n)) atTop ≤ ∫ x, f x ∂μ := by sorry

end BERicci.Contract
