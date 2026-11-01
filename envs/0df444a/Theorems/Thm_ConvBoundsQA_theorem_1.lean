-- Prove2me | Theorems.Thm_ConvBoundsQA_theorem_1
-- name    : ConvBoundsQA.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:57.609424+00:00
-- url     : https://prove2.me/theorems/08f949ed-36bf-4785-abdd-199af6c1f35e
-- title:
--   Theorem 1 — convolution bound on RVaR aggregation (corrected: $\Delta_n$ allows $\beta_0=1$)
-- statement:
--   Let $\mu=(\mu_1,\dots,\mu_n)$ be Borel probability measures on $\mathbb R$ and $0\le t<t+s\le1$. Then
--   $$
--   \sup_{\nu\in\Lambda(\mu)}R_{t,s}(\nu)\ \le\ \inf_{\substack{\beta\in(t+s)\Delta_n'\\ \beta_0\ge s}}\ \sum_{i=1}^nR_{\beta_i,\beta_0}(\mu_i),\tag{12}
--   $$
--   where $\beta$ ranges over $\beta_0\in[s,t+s]$, $\beta_1,\dots,\beta_n\ge0$ with $\sum_{i=0}^n\beta_i=t+s$, and the infimum is over the $\beta$ whose sum is well defined. Moreover, (12) holds with equality in each of the following cases:
--
--   1. $t=0$;
--   2. each of $\mu_1,\dots,\mu_n$ admits a decreasing density beyond its $(1-t-s)$-quantile, i.e. each $\mu_i^{(1-t-s)+}$ admits a decreasing density;
--   3. $\displaystyle\sum_{i=1}^n\mu_i\bigl(q^+_{1-t-s}(\mu_i),\,q^-_1(\mu_i)\bigr]\le t+s$.
--
--   When $(t,s)=(0,1)$ the functional $R_{0,1}$ is the mean; for that pair it is assumed that every mean $R_{0,1}(\mu_i)$ is defined and the means do not contain both $+\infty$ and $-\infty$.
--
--   This is the convolution bound on worst-case RVaR aggregation with given marginals, and its sharpness in three cases.
--
--   **Formalization Note** Suprema and infima are in `EReal`; "decreasing" means non-increasing.
--
--   Differences from the source:
--   - correction: the parameter set $\{\beta\in(t+s)\Delta_n:\beta_0\ge s>0\}$, in which $\beta_0<t+s$ → $\beta_0\in[s,t+s]$ (the set $(t+s)\Delta_n'$ with $\beta_0\ge s$), as in (11); reason: with the printed set case (i) is false: $n=1$, $\mu_1=\delta_0$, $t=0$, $s=1/2$ satisfy every assumption, the left side is $0$ and the set is empty, so the infimum is $+\infty$; (11) on p.8 and the proof on p.39 use $\beta=(s,0,\dots,0)$
--   - reading: an infimum of sums that may contain both $+\infty$ and $-\infty$ → the infimum over the $\beta$ whose terms are defined and do not contain both $\pm\infty$; reason: the sums in (10) are used only when well defined (p.8); this equals valuing an undefined sum $+\infty$, while plain extended-real addition ($-\infty+\infty=-\infty$) would make (12) false
--   - generalization: $R_{0,1}$ is the mean, defined only on $\mathcal M_1$ (p.7) → for $(t,s)=(0,1)$ only: every $R_{0,1}(\mu_i)$ is defined and the means do not contain both $\pm\infty$; reason: for $(t,s)=(0,1)$ the statement covers marginals whose means are defined but possibly $\pm\infty$ (no $\infty-\infty$ among them), beyond the finite means of $\mathcal M_1$; there $\mathbb E[\sum_i X_i]=\sum_i\mathbb E[X_i]$ for every coupling, and on $\mathcal M_1^n$ it is the statement of the source
--   - reading: “admits a decreasing density” (p.9) → a density vanishing below some $a$ and non-increasing on $(a,\infty)$; reason: “decreasing” read as non-increasing, the more general reading; the support is the interval where the density is positive, as in Wang and Wang (2016) and Jakobsons et al. (2016)
--   - encoding: quantiles and RVaR values in $[-\infty,\infty]$ → `EReal`, with $R_{\beta,\alpha}$ the difference of the integrals of the positive and negative parts of the quantile; reason: Lean convention; same values wherever the source defines them
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, Theorem 1, (12), p.9; (11), p.8; proof pp.39–41

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

/-- Theorem 1 (convolution bound on RVaR aggregation), with the parameter set corrected so that
`β₀ = t + s` is allowed: let `μ = (μ₁, …, μₙ) ∈ Mⁿ`. For any `t, s` with `0 ⩽ t < t + s ⩽ 1`,
`sup_{ν ∈ Λ(μ)} R_{t,s}(ν) ⩽ inf_{β ∈ (t+s)Δₙ, β₀ ⩾ s > 0} Σ_{i=1}^n R_{βᵢ,β₀}(μᵢ)` (12), and (12)
holds as an equality when (i) `t = 0`; (ii) each `μᵢ` admits a decreasing density beyond its
`(1 − t − s)`-quantile; (iii) `Σ_{i=1}^n μᵢ(q⁺_{1−t−s}(μᵢ), q⁻₁(μᵢ)] ⩽ t + s`
(Blanchet, Lam, Liu, Wang, *Convolution Bounds on Quantile Aggregation*, arXiv:2007.09320v5,
Theorem 1, p.9; (11), p.8; proof on pp.39–41).

**Formalization Note** The parameter set is `(t + s) • DeltaCorr n` with `β₀ ⩾ s`, i.e. `β₀ ∈ [s, t + s]`,
`βᵢ ⩾ 0`, `Σ_{i=0}^n βᵢ = t + s`, as in (11) on p.8. The printed `(t + s)Δₙ` requires `β₀ < t + s`,
which makes the set empty at `t = 0` and case (i) false (`n = 1`, `μ₁ = δ₀`, `t = 0`, `s = 1/2`:
the left side is `0`, the infimum over the empty set is `+∞`); the proof on p.39 uses
`β = (s, 0, …, 0)`. The infimum is `convBound`: it leaves out the `β` whose terms contain both `+∞`
and `−∞`. The suprema and infima are in `EReal`. At `(t, s) = (0, 1)` the functional `R_{0,1}` is the
mean, defined only on `M₁` (p.7); the hypothesis `hmean` requires, for that pair only, that each mean
`R_{0,1}(μᵢ)` is defined and the means do not contain both `+∞` and `−∞`. The interval in (iii) is
`q⁺_{1−t−s}(μᵢ) < x ⩽ q⁻₁(μᵢ)` in `EReal` (open left, closed right, as printed), and "beyond its
`(1 − t − s)`-quantile" means that `μᵢ^{(1−t−s)+} = tailDist (μ i) (1 − t − s)` admits a decreasing
density (p.10). -/
theorem theorem_1 {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (t s : ℝ) (ht : 0 ≤ t) (hts : t < t + s) (hts1 : t + s ≤ 1)
    (hmean : t = 0 → s = 1 → (∀ i, RDefined 0 1 (μ i)) ∧ NoInfMinusInf (fun i => R 0 1 (μ i))) :
    (⨆ ν ∈ Lam μ, R t s ν) ≤ convBound μ ((t + s) • DeltaCorr n ∩ {β | s ≤ β.1}) ∧
      (t = 0 → (⨆ ν ∈ Lam μ, R t s ν) = convBound μ ((t + s) • DeltaCorr n ∩ {β | s ≤ β.1})) ∧
      ((∀ i, AdmitsDecDensity (tailDist (μ i) (1 - t - s))) →
        (⨆ ν ∈ Lam μ, R t s ν) = convBound μ ((t + s) • DeltaCorr n ∩ {β | s ≤ β.1})) ∧
      (∑ i, μ i {x : ℝ | qPlus (1 - t - s) (μ i) < (x : EReal) ∧ (x : EReal) ≤ qMinus 1 (μ i)} ≤
          ENNReal.ofReal (t + s) →
        (⨆ ν ∈ Lam μ, R t s ν) = convBound μ ((t + s) • DeltaCorr n ∩ {β | s ≤ β.1})) := by sorry

end ConvBoundsQA
