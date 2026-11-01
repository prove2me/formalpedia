-- Prove2me | Theorems.Thm_ConvBoundsQA_proposition_1
-- name    : ConvBoundsQA.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:47.37538+00:00
-- url     : https://prove2.me/theorems/82c9207e-aa22-4a4a-812d-1077da4620c1
-- title:
--   Proposition 1 — reduction to level 0 through tail distributions
-- statement:
--   Let $\mu=(\mu_1,\dots,\mu_n)$ be Borel probability measures on $\mathbb R$, $t\in[0,1)$ and $s\in(0,1-t]$. Then
--   $$
--   \sup_{\nu\in\Lambda(\mu)}R_{t,s}(\nu)=\sup_{\nu\in\Lambda(\mu^{(1-t-s)+})}\mathrm{LES}_{s/(t+s)}(\nu)
--   \qquad\text{and}\qquad
--   \sup_{\nu\in\Lambda(\mu)}q^+_t(\nu)=\sup_{\nu\in\Lambda(\mu^{t+})}q^+_0(\nu),
--   $$
--   where $\mu^{t+}=(\mu_1^{t+},\dots,\mu_n^{t+})$.
--
--   Worst-case RVaR and quantile aggregation at any level therefore reduce to the corresponding problems at quantile level $0$ (LES and essential infimum) for the tail marginals.
--
--   **Formalization Note** Suprema are taken in `EReal`.
--
--   Differences from the source:
--   - encoding: quantiles and RVaR values in $[-\infty,\infty]$ → `EReal`, with $R_{\beta,\alpha}$ the difference of the integrals of the positive and negative parts of the quantile; reason: Lean convention; same values wherever the source defines them
--   - generalization: at $(t,s)=(0,1)$ both suprema are of $R_{0,1}$, defined only on $\mathcal M_1$ → the identity for all marginals, with $R_{0,1}=-\infty$ where the mean is undefined; reason: there both sides are suprema of the same functional over $\Lambda(\mu^{0+})=\Lambda(\mu)$; elsewhere every value is defined
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, Proposition 1, p.10

import Mathlib
import Definitions.Def_ConvBoundsQA_qPlus
import Definitions.Def_ConvBoundsQA_R
import Definitions.Def_ConvBoundsQA_Lam
import Definitions.Def_ConvBoundsQA_tailDist

open MeasureTheory

namespace ConvBoundsQA

/-- Proposition 1: for `μ = (μ₁, …, μₙ) ∈ Mⁿ`, `t ∈ [0, 1)` and `s ∈ (0, 1 − t]`,
`sup_{ν ∈ Λ(μ)} R_{t,s}(ν) = sup_{ν ∈ Λ(μ^{(1−t−s)+})} LES_{s/(t+s)}(ν)` and
`sup_{ν ∈ Λ(μ)} q⁺_t(ν) = sup_{ν ∈ Λ(μ^{t+})} q⁺_0(ν)`
(Blanchet, Lam, Liu, Wang, *Convolution Bounds on Quantile Aggregation*, arXiv:2007.09320v5,
Proposition 1, p.10).

**Formalization Note** `μ^{t+} = (μ₁^{t+}, …, μₙ^{t+})` is `fun i => tailDist (μ i) t`. Suprema are
taken in `EReal`. `R` is total in Lean: at `(t, s) = (0, 1)` both sides are suprema of `R_{0,1}` (the
mean, `−∞` where undefined) over the same set `Λ(μ^{0+}) = Λ(μ)`, and the identity is stated for that
value as well. -/
theorem proposition_1 {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (t s : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hs : s ∈ Set.Ioc 0 (1 - t)) :
    (⨆ ν ∈ Lam μ, R t s ν) =
        (⨆ ν ∈ Lam (fun i => tailDist (μ i) (1 - t - s)), LES (s / (t + s)) ν) ∧
      (⨆ ν ∈ Lam μ, qPlus t ν) = (⨆ ν ∈ Lam (fun i => tailDist (μ i) t), qPlus 0 ν) := by sorry

end ConvBoundsQA
