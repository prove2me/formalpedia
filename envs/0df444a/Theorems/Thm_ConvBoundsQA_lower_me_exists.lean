-- Prove2me | Theorems.Thm_ConvBoundsQA_lower_me_exists
-- name    : ConvBoundsQA.lower_me_exists
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:58.272249+00:00
-- url     : https://prove2.me/theorems/78a93bf4-88d4-47b7-86af-2ce283abe0e1
-- title:
--   Proof of Theorem 1(iii) — a lower mutually exclusive coupling exists
-- statement:
--   Let $\mu=(\mu_1,\dots,\mu_n)$ be Borel probability measures on $\mathbb R$ with
--   $$
--   \sum_{i=1}^n\mu_i\bigl(q^+_0(\mu_i),\,q^-_1(\mu_i)\bigr]\le1 .
--   $$
--   Then there is a lower mutually exclusive random vector $(X_1,\dots,X_n)$ with $X_i\sim\mu_i$ for every $i$: a coupling $\pi\in\Gamma(\mu)$ under which almost surely at most one coordinate exceeds its essential infimum.
--
--   This is the dependence structure that attains the bound in Theorem 1(iii).
--
--   **Formalization Note** The interval is open at the essential infimum and closed at the essential supremum, compared in `EReal`; masses are summed in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: random vectors $(X_1,\dots,X_n)$ with $X_i\sim\mu_i$ on an atomless probability space → their joint laws $\pi\in\Gamma(\mu)$, probability measures on `Fin n → ℝ`, and $\sum_i X_i$ by the image law $\lambda_\pi$; reason: every statement involved depends only on the joint law
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, p.41, proof of Theorem 1(iii)

import Mathlib
import Definitions.Def_ConvBoundsQA_qPlus
import Definitions.Def_ConvBoundsQA_Lam
import Definitions.Def_ConvBoundsQA_LowerME

open MeasureTheory

namespace ConvBoundsQA

/-- Proof of Theorem 1(iii), p.41: the assumption `Σ_{i=1}^n μᵢ(q⁺₀(μᵢ), q⁻₁(μᵢ)] ⩽ 1` allows for the
existence of a lower mutually exclusive random vector `(X₁, …, Xₙ)` with `Xᵢ ∼ μᵢ`
(Blanchet, Lam, Liu, Wang, *Convolution Bounds on Quantile Aggregation*, arXiv:2007.09320v5, p.41).

**Formalization Note** The interval `(q⁺₀(μᵢ), q⁻₁(μᵢ)]` is the set of reals `x` with
`q⁺₀(μᵢ) < x ⩽ q⁻₁(μᵢ)` in `EReal` (open at the left end, closed at the right end, as printed). The
random vector is its law `π ∈ Γ(μ)`. -/
theorem lower_me_exists {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : ∑ i, μ i {x : ℝ | qPlus 0 (μ i) < (x : EReal) ∧ (x : EReal) ≤ qMinus 1 (μ i)} ≤ 1) :
    ∃ π ∈ Gam μ, LowerME μ π := by sorry

end ConvBoundsQA
