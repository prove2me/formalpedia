-- Prove2me | Theorems.Thm_ConvBoundsQA_lemma_EC_1
-- name    : ConvBoundsQA.lemma_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:19.339987+00:00
-- url     : https://prove2.me/theorems/8614689d-a20d-4fb2-81f2-790d386fb31f
-- title:
--   Lemma EC.1 — RVaR aggregation inequality without finite means
-- statement:
--   Let $n\ge1$, $\alpha_1,\dots,\alpha_n\in(0,1]$, $\beta_1,\dots,\beta_n\in[0,1]$, $b=\sum_{i=1}^n\beta_i$ and $a=\max_i\alpha_i$, with $b+a\le1$. Let $\mu=(\mu_1,\dots,\mu_n)$ be Borel probability measures on $\mathbb R$ and suppose the sum $\sum_i R_{\beta_i,\alpha_i}(\mu_i)$ is well defined: every term is defined and the terms do not contain both $+\infty$ and $-\infty$. Then for every $\nu\in\Lambda(\mu)$,
--   $$
--   R_{b,a}(\nu)\le\sum_{i=1}^nR_{\beta_i,\alpha_i}(\mu_i).
--   $$
--
--   This extends the RVaR inequality of Embrechts, Liu and Wang (2018) to distributions without finite mean; it is the inequality from which the convolution bounds (11), (12) and (14) are derived.
--
--   **Formalization Note** $\nu\in\Lambda(\mu)$ is the law of $X_1+\dots+X_n$ for some coupling of the $\mu_i$; RVaR values are extended reals.
--
--   Differences from the source:
--   - encoding: $\alpha_1,\dots,\alpha_n\in[0,1]$ → $\alpha_i\in(0,1]$; reason: $R_{\beta_i,0}$ is not defined by (6) (it divides by $\alpha$), so a zero $\alpha_i$ only makes the right-hand side undefined
--   - encoding: $n\in\mathbb N$ → $n\ge 1$; reason: the paper's $\mathbb N$ starts at $1$; at $n=0$ the objects are empty or undefined
--   - reading: the right-hand side is well-defined (no “$\infty-\infty$”) → every $R_{\beta_i,\alpha_i}(\mu_i)$ is defined and the terms do not contain both $+\infty$ and $-\infty$; reason: these are exactly the conditions under which the extended-real sum has a value
--   - encoding: quantiles and RVaR values in $[-\infty,\infty]$ → `EReal`, with $R_{\beta,\alpha}$ the difference of the integrals of the positive and negative parts of the quantile; reason: Lean convention; same values wherever the source defines them
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, Lemma EC.1, (EC.1), p.38

import Mathlib
import Definitions.Def_ConvBoundsQA_R
import Definitions.Def_ConvBoundsQA_Lam

open MeasureTheory

namespace ConvBoundsQA

/-- Lemma EC.1: let `α₁, …, αₙ, β₁, …, βₙ ∈ [0, 1]`, `b = Σᵢ βᵢ` and `a = ⋁ᵢ αᵢ`. If `b + a ⩽ 1`,
then for all `μ ∈ Mⁿ` and `ν ∈ Λ(μ)`, `R_{b,a}(ν) ⩽ Σ_{i=1}^n R_{βᵢ,αᵢ}(μᵢ)`, provided the right-hand
side is well defined (no "`∞ − ∞`")
(Blanchet, Lam, Liu, Wang, *Convolution Bounds on Quantile Aggregation*, arXiv:2007.09320v5,
Lemma EC.1, (EC.1), p.38).

**Formalization Note** `n ⩾ 1`, and every `αᵢ > 0`, since `R_{βᵢ,0}` is not defined by (6). The maximum
`a` is the real `⨆ i, α i` over the finite nonempty index set. "Well defined" means every
`R_{βᵢ,αᵢ}(μᵢ)` is defined and the terms do not contain both `+∞` and `−∞`. -/
theorem lemma_EC_1 {n : ℕ} (hn : 0 < n) (α β : Fin n → ℝ) (hα : ∀ i, α i ∈ Set.Ioc 0 1)
    (hβ : ∀ i, β i ∈ Set.Icc 0 1) (hba : ∑ i, β i + ⨆ i, α i ≤ 1)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hdef : (∀ i, RDefined (β i) (α i) (μ i)) ∧ NoInfMinusInf (fun i => R (β i) (α i) (μ i)))
    (ν : Measure ℝ) (hν : ν ∈ Lam μ) :
    R (∑ i, β i) (⨆ i, α i) ν ≤ ∑ i, R (β i) (α i) (μ i) := by sorry

end ConvBoundsQA
