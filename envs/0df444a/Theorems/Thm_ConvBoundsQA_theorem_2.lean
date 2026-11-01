-- Prove2me | Theorems.Thm_ConvBoundsQA_theorem_2
-- name    : ConvBoundsQA.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:55.521469+00:00
-- url     : https://prove2.me/theorems/9de2003c-0f45-4cc6-befa-c042252f14e7
-- title:
--   Theorem 2 — convolution bound on quantile aggregation, sharp in five cases
-- statement:
--   Let $n\ge1$, $\mu=(\mu_1,\dots,\mu_n)$ be Borel probability measures on $\mathbb R$ (no moment, density or support assumption) and $t\in[0,1)$. Then
--   $$
--   \sup_{\nu\in\Lambda(\mu)}q^+_t(\nu)\ \le\ \inf_{\beta\in(1-t)\Delta_n}\ \sum_{i=1}^nR_{\beta_i,\beta_0}(\mu_i),\tag{14}
--   $$
--   where $\beta=(\beta_0,\beta_1,\dots,\beta_n)$ ranges over $\beta_0\in(0,1-t)$, $\beta_i\in[0,1-t)$ with $\sum_{i=0}^n\beta_i=1-t$, and the infimum is over the $\beta$ whose sum is well defined. Moreover, (14) holds with equality in each of the following cases:
--
--   1. $n\le2$;
--   2. each of $\mu_1,\dots,\mu_n$ admits a decreasing density beyond its $t$-quantile;
--   3. each of $\mu_1,\dots,\mu_n$ admits an increasing density beyond its $t$-quantile;
--   4. $\displaystyle\sum_{i=1}^n\mu_i\bigl(q^+_t(\mu_i),\,q^-_1(\mu_i)\bigr]\le1-t$;
--   5. $\displaystyle\sum_{i=1}^n\mu_i\bigl[q^+_t(\mu_i),\,q^-_1(\mu_i)\bigr)\le1-t$.
--
--   The left side is the worst-case Value-at-Risk of a sum of risks with known marginals and unknown dependence; the right side, the convolution bound, depends only on the marginals and is computed from an $(n+1)$-dimensional optimization.
--
--   **Formalization Note** Couplings are probability measures on `Fin n → ℝ` and $\Lambda(\mu)$ the laws of the coordinate sum. Quantiles, RVaR, the supremum and the infimum are in `EReal`. "Beyond its $t$-quantile" means the density condition for the tail distribution $\mu_i^{t+}$; "decreasing"/"increasing" mean non-increasing/non-decreasing. The masses in cases 4 and 5 are summed in $[0,\infty]$ and the interval ends are compared in `EReal`.
--
--   Differences from the source:
--   - reading: an infimum of sums that may contain both $+\infty$ and $-\infty$ (possible at $t=0$) → the infimum over the $\beta$ whose terms do not contain both $\pm\infty$; reason: the paper's sums are used only when well defined (p.8); this equals valuing an undefined sum $+\infty$, while plain extended-real addition ($-\infty+\infty=-\infty$) would make (14) false for two Cauchy marginals
--   - reading: “admits a decreasing (increasing) density” (p.9) → a density vanishing below some $a$ and non-increasing on $(a,\infty)$ (resp. vanishing above some $b$ and non-decreasing on $(-\infty,b)$); reason: “decreasing” read as non-increasing, the more general reading; the support is the interval where the density is positive, as in Wang and Wang (2016) and Jakobsons et al. (2016)
--   - encoding: $n\in\mathbb N$ → $n\ge 1$; reason: the paper's $\mathbb N$ starts at $1$; at $n=0$ the objects are empty or undefined
--   - encoding: quantiles and RVaR values in $[-\infty,\infty]$ → `EReal`, with $R_{\beta,\alpha}$ the difference of the integrals of the positive and negative parts of the quantile; reason: Lean convention; same values wherever the source defines them
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, Theorem 2, (14), p.11

import Mathlib
import Definitions.Def_ConvBoundsQA_qPlus
import Definitions.Def_ConvBoundsQA_R
import Definitions.Def_ConvBoundsQA_Lam
import Definitions.Def_ConvBoundsQA_Delta
import Definitions.Def_ConvBoundsQA_convBound
import Definitions.Def_ConvBoundsQA_tailDist
import Definitions.Def_ConvBoundsQA_AdmitsDecDensity

open MeasureTheory
open scoped Pointwise

namespace ConvBoundsQA

/-- Theorem 2 (convolution bound on quantile aggregation): for `μ = (μ₁, …, μₙ) ∈ Mⁿ` and
`t ∈ [0, 1)`,
`sup_{ν ∈ Λ(μ)} q⁺_t(ν) ⩽ inf_{β ∈ (1−t)Δₙ} Σ_{i=1}^n R_{βᵢ,β₀}(μᵢ)` (14), and (14) holds as an
equality in the following cases: (i) `n ⩽ 2`; (ii) each of `μ₁, …, μₙ` admits a decreasing density
beyond its `t`-quantile; (iii) each of `μ₁, …, μₙ` admits an increasing density beyond its
`t`-quantile; (iv) `Σ_{i=1}^n μᵢ(q⁺_t(μᵢ), q⁻₁(μᵢ)] ⩽ 1 − t`; (v)
`Σ_{i=1}^n μᵢ[q⁺_t(μᵢ), q⁻₁(μᵢ)) ⩽ 1 − t`
(Blanchet, Lam, Liu, Wang, *Convolution Bounds on Quantile Aggregation*, arXiv:2007.09320v5,
Theorem 2, (14), p.11).

**Formalization Note** `n ⩾ 1`; `μᵢ` are arbitrary Borel probability measures on `ℝ` (no moment,
density or support assumption). Couplings are probability measures on `Fin n → ℝ` with the given
marginals (`Gam`), and `Λ(μ)` is the set of laws of the coordinate sum (`Lam`). Quantiles, `R` and the
supremum and infimum are in `EReal`. The parameter set is the printed `(1 − t)Δₙ` (`β₀ ∈ (0, 1 − t)`,
`βᵢ ∈ [0, 1 − t)`, `Σ_{i=0}^n βᵢ = 1 − t`), with `β = (β₀, (β₁, …, βₙ))`. The infimum is `convBound`:
a `β` whose terms contain both `+∞` and `−∞` (possible at `t = 0`) is left out, the same as valuing
that sum `+∞`. "Beyond its `t`-quantile" means that `μᵢ^{t+} = tailDist (μ i) t` admits the density
(p.10); "decreasing"/"increasing" are non-increasing/non-decreasing. The interval in (iv) is
`q⁺_t(μᵢ) < x ⩽ q⁻₁(μᵢ)` and in (v) `q⁺_t(μᵢ) ⩽ x < q⁻₁(μᵢ)`, compared in `EReal`, with the masses
summed in `[0, ∞]`. -/
theorem theorem_2 {n : ℕ} (hn : 0 < n) (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (⨆ ν ∈ Lam μ, qPlus t ν) ≤ convBound μ ((1 - t) • Delta n) ∧
      (n ≤ 2 → (⨆ ν ∈ Lam μ, qPlus t ν) = convBound μ ((1 - t) • Delta n)) ∧
      ((∀ i, AdmitsDecDensity (tailDist (μ i) t)) →
        (⨆ ν ∈ Lam μ, qPlus t ν) = convBound μ ((1 - t) • Delta n)) ∧
      ((∀ i, AdmitsIncDensity (tailDist (μ i) t)) →
        (⨆ ν ∈ Lam μ, qPlus t ν) = convBound μ ((1 - t) • Delta n)) ∧
      (∑ i, μ i {x : ℝ | qPlus t (μ i) < (x : EReal) ∧ (x : EReal) ≤ qMinus 1 (μ i)} ≤
          ENNReal.ofReal (1 - t) →
        (⨆ ν ∈ Lam μ, qPlus t ν) = convBound μ ((1 - t) • Delta n)) ∧
      (∑ i, μ i {x : ℝ | qPlus t (μ i) ≤ (x : EReal) ∧ (x : EReal) < qMinus 1 (μ i)} ≤
          ENNReal.ofReal (1 - t) →
        (⨆ ν ∈ Lam μ, qPlus t ν) = convBound μ ((1 - t) • Delta n)) := by sorry

end ConvBoundsQA
