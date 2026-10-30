-- Prove2me | Theorems.Thm_ChenGallegoPricing_ABE_lemma_2
-- name    : ChenGallegoPricing.ABE.lemma_2
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T05:32:25.172102+00:00
-- url     : https://prove2.me/theorems/169dac73-fcde-49f2-aace-9242b3e07787
-- title:
--   Lemma 2 — unchanged sub-Gaussian parameter under bin mixing
-- statement:
--   Let $\mu$ be a probability measure on a measurable space $X$, let $B$ be measurable with $\mu(B)>0$, and let $\kappa_x$ be a measurable family of real probability laws. Fix $\sigma\ge0$. Suppose each component with $x\in B$ has a finite first moment $m(x)$ and satisfies
--   $$\mathbb E_{\kappa_x}e^{t(Z-m(x))}\le e^{\sigma t^2}\qquad(t\in\mathbb R),$$
--   with finite exponential moments. Let $\eta=\int\kappa_x\,\mu(dx\mid B)$ and assume its first moment is finite. The printed assertion is that
--   $$\mathbb E_\eta e^{t(Z-\mathbb E_\eta Z)}\le e^{\sigma t^2}\qquad(t\in\mathbb R),$$
--   including existence of the finite exponential moments. No equal-component-means hypothesis is imposed. The price is fixed throughout and is suppressed from the notation. This is the source's assertion; insight I1 records its bounded counterexample.
--
--   Differences from the source:
--   - encoding: the displayed means and conditional distribution → finite first moments and conditioning on a positive-probability measurable event; a Markov kernel represents the family at the fixed price; reason: these are the domains where the source’s displayed expectations and conditioning are defined
--   - encoding: the bound exp(σt²) → Mathlib HasSubgaussianMGF for the centered variable with variance proxy 2σ, including integrability of every exponential; reason: Mathlib uses exp(c t²/2); this preserves σ exactly and avoids default-zero nonintegrable expectations
--   - generalization: a componentwise bound for given covariates in the model → arbitrary measurable mixing space and component hypotheses required only on B; reason: values outside the conditioning event have no effect; the original covariate-space claim is a specialization
-- source:
--   Chen and Gallego, Nonparametric Pricing Analytics with Customer Covariates, arXiv:1805.01136v3 (16 February 2020), https://arxiv.org/abs/1805.01136v3; Lemma 2, printed/PDF p. 27

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ChenGallegoPricing.ABE

theorem lemma_2 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (B : Set X)
    (hB : MeasurableSet B) (hpos : μ B ≠ 0)
    (κ : Kernel X ℝ) [IsMarkovKernel κ] (σ : ℝ≥0)
    (hcomponents : ∀ x ∈ B, Integrable id (κ x) ∧
      HasSubgaussianMGF (fun z => z - ∫ y, y ∂κ x) (2 * σ) (κ x))
    (hmean : Integrable id (κ ∘ₘ ProbabilityTheory.cond μ B)) :
    HasSubgaussianMGF
      (fun z => z - ∫ y, y ∂(κ ∘ₘ ProbabilityTheory.cond μ B))
      (2 * σ) (κ ∘ₘ ProbabilityTheory.cond μ B) := by sorry

end ChenGallegoPricing.ABE
