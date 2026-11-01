-- Prove2me | Theorems.Thm_ConvBoundsQA_lemma_EC_2
-- name    : ConvBoundsQA.lemma_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:58.556999+00:00
-- url     : https://prove2.me/theorems/06b93af5-5d8f-4c66-85bb-54dd06f8e019
-- title:
--   Lemma EC.2 — LES of a lower mutually exclusive sum
-- statement:
--   Let $n\ge1$, let $(X_1,\dots,X_n)$ be lower mutually exclusive with $X_i\sim\mu_i$, and let every $X_i$ be bounded from below. Then for every $\alpha\in(0,1)$ there are $\beta_1,\dots,\beta_n\in[0,1)$ with $\sum_{i=1}^n\beta_i=1-\alpha$ such that
--   $$
--   R_{1-\alpha,\alpha}\Bigl(\sum_{i=1}^nX_i\Bigr)=\sum_{i=1}^nR_{\beta_i,\alpha}(X_i).
--   $$
--
--   For a lower mutually exclusive vector the left-tail expected shortfall of the sum is a sum of RVaRs of the components; this shows that the convolution bound is attained in case (iii) of Theorem 1.
--
--   **Formalization Note** The random vector is its joint law $\pi\in\Gamma(\mu)$, and the left side is $R_{1-\alpha,\alpha}$ of the aggregate law $\lambda_\pi$.
--
--   Differences from the source:
--   - encoding: random vectors $(X_1,\dots,X_n)$ with $X_i\sim\mu_i$ on an atomless probability space → their joint laws $\pi\in\Gamma(\mu)$, probability measures on `Fin n → ℝ`, and $\sum_i X_i$ by the image law $\lambda_\pi$; reason: every statement involved depends only on the joint law
--   - encoding: $X_i$ bounded from below → $q^+_0(\mu_i)>-\infty$; reason: a random variable is a.s. bounded below exactly when its essential infimum is finite
--   - encoding: $n\in\mathbb N$ → $n\ge 1$; reason: the paper's $\mathbb N$ starts at $1$; at $n=0$ the objects are empty or undefined
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, Lemma EC.2, (EC.5), pp.41–42

import Mathlib
import Definitions.Def_ConvBoundsQA_qPlus
import Definitions.Def_ConvBoundsQA_R
import Definitions.Def_ConvBoundsQA_Lam
import Definitions.Def_ConvBoundsQA_LowerME

open MeasureTheory

namespace ConvBoundsQA

/-- Lemma EC.2: if random variables `X₁, …, Xₙ` are lower mutually exclusive and bounded from below,
then for `α ∈ (0, 1)`, `R_{1−α,α}(Σᵢ Xᵢ) = Σᵢ R_{βᵢ,α}(Xᵢ)` for some `β₁, …, βₙ ∈ [0, 1)` with
`Σᵢ βᵢ = 1 − α`
(Blanchet, Lam, Liu, Wang, *Convolution Bounds on Quantile Aggregation*, arXiv:2007.09320v5,
Lemma EC.2, (EC.5), pp.41–42).

**Formalization Note** The random vector is its joint law `π ∈ Γ(μ)` with `μᵢ` the law of `Xᵢ`, and
`R(Σᵢ Xᵢ)` is `R` of the aggregate law `λ_π`. "Bounded from below" is `q⁺₀(μᵢ) > −∞` for every `i`
(the essential infimum is finite). `n ⩾ 1`. -/
theorem lemma_EC_2 {n : ℕ} (hn : 0 < n) (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (π : Measure (Fin n → ℝ)) (hπ : π ∈ Gam μ) (hME : LowerME μ π)
    (hbdd : ∀ i, qPlus 0 (μ i) ≠ ⊥) (α : ℝ) (hα : α ∈ Set.Ioo 0 1) :
    ∃ β : Fin n → ℝ, (∀ i, β i ∈ Set.Ico 0 1) ∧ ∑ i, β i = 1 - α ∧
      R (1 - α) α (aggLaw π) = ∑ i, R (β i) α (μ i) := by sorry

end ConvBoundsQA
