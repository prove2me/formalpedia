-- Prove2me | Theorems.Thm_ConvBoundsQA_upper_me
-- name    : ConvBoundsQA.upper_me
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:38.790143+00:00
-- url     : https://prove2.me/theorems/227cb9bd-f586-471c-a1da-c46ecc85a183
-- title:
--   Proof of Theorem 2(v) — upper mutually exclusive coupling and its essential infimum
-- statement:
--   Let $n\ge1$ and $\mu=(\mu_1,\dots,\mu_n)$ be Borel probability measures on $\mathbb R$.
--
--   1. If $\displaystyle\sum_{i=1}^n\mu_i\bigl[q^+_0(\mu_i),\,q^-_1(\mu_i)\bigr)\le1$, there is an upper mutually exclusive random vector $(X_1,\dots,X_n)$ with $X_i\sim\mu_i$.
--   2. For every upper mutually exclusive $(X_1,\dots,X_n)$ with $X_i\sim\mu_i$,
--   $$
--   q^+_0\Bigl(\sum_{i=1}^nX_i\Bigr)=\min_{1\le i\le n}\Bigl(q^+_0(\mu_i)+\sum_{j\ne i}q^-_1(\mu_j)\Bigr).
--   $$
--
--   Under upper mutual exclusivity the essential infimum of the sum is explicit; this attains the convolution bound in case (v) of Theorem 2.
--
--   **Formalization Note** The interval is closed at the essential infimum and open at the essential supremum, compared in `EReal`. The minimum and sums are in `EReal`; for an upper mutually exclusive vector $\sum_i\mu_i(-\infty,q^-_1(\mu_i))\le1$, so no term contains both $-\infty$ and $+\infty$. The trailing inequality "$\ge\inf_{\beta\in\Delta_n}\dots$" on p.44 is a step of the proof and not part of this statement.
--
--   Differences from the source:
--   - encoding: random vectors $(X_1,\dots,X_n)$ with $X_i\sim\mu_i$ on an atomless probability space → their joint laws $\pi\in\Gamma(\mu)$, probability measures on `Fin n → ℝ`, and $\sum_i X_i$ by the image law $\lambda_\pi$; reason: every statement involved depends only on the joint law
--   - encoding: $n\in\mathbb N$ → $n\ge 1$; reason: the paper's $\mathbb N$ starts at $1$; at $n=0$ the objects are empty or undefined
--   - generalization: the essential-infimum formula for the vector obtained under the assumption of (v) → the formula for every upper mutually exclusive coupling; reason: the page's derivation uses only upper mutual exclusivity; it specializes to the page's vector
--   - encoding: quantiles and RVaR values in $[-\infty,\infty]$ → `EReal`, with $R_{\beta,\alpha}$ the difference of the integrals of the positive and negative parts of the quantile; reason: Lean convention; same values wherever the source defines them
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, p.44, proof of Theorem 2(v)

import Mathlib
import Definitions.Def_ConvBoundsQA_qPlus
import Definitions.Def_ConvBoundsQA_Lam
import Definitions.Def_ConvBoundsQA_LowerME

open MeasureTheory

namespace ConvBoundsQA

/-- Proof of Theorem 2(v), p.44: (a) the assumption `Σ_{i=1}^n μᵢ[q⁺₀(μᵢ), q⁻₁(μᵢ)) ⩽ 1` allows for the
existence of an upper mutually exclusive random vector `(X₁, …, Xₙ)` with `Xᵢ ∼ μᵢ`; (b) for such a
vector, `q⁺₀(Σᵢ Xᵢ) = min_{1⩽i⩽n} (q⁺₀(μᵢ) + Σ_{j≠i} q⁻₁(μⱼ))`
(Blanchet, Lam, Liu, Wang, *Convolution Bounds on Quantile Aggregation*, arXiv:2007.09320v5, p.44).

**Formalization Note** The interval `[q⁺₀(μᵢ), q⁻₁(μᵢ))` is the set of reals `x` with
`q⁺₀(μᵢ) ⩽ x < q⁻₁(μᵢ)` in `EReal` (closed at the left end, open at the right end, as printed). The
random vector is its law `π ∈ Γ(μ)` and `Σᵢ Xᵢ` has law `λ_π`. Clause (b) is stated for every upper
mutually exclusive `π ∈ Γ(μ)`; the minimum is the `EReal` infimum over `i`, and `n ⩾ 1`. The sums are
`EReal` sums; for an upper mutually exclusive coupling `Σᵢ μᵢ(−∞, q⁻₁(μᵢ)) ⩽ 1`, so no term
`q⁺₀(μᵢ) + Σ_{j≠i} q⁻₁(μⱼ)` contains both `−∞` and `+∞`. The trailing "`⩾ inf …`" on p.44 is a step
of the proof and not part of this statement. -/
theorem upper_me {n : ℕ} (hn : 0 < n) (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    (∑ i, μ i {x : ℝ | qPlus 0 (μ i) ≤ (x : EReal) ∧ (x : EReal) < qMinus 1 (μ i)} ≤ 1 →
        ∃ π ∈ Gam μ, UpperME μ π) ∧
      (∀ π ∈ Gam μ, UpperME μ π →
        qPlus 0 (aggLaw π) = ⨅ i, (qPlus 0 (μ i) + ∑ j ∈ Finset.univ.erase i, qMinus 1 (μ j))) := by sorry

end ConvBoundsQA
