-- Prove2me | Theorems.Thm_DynPricingCov_lemma_4
-- name    : DynPricingCov.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:02:57.554721+00:00
-- url     : https://prove2.me/theorems/05a9fc5f-ee72-45d3-8342-430e6e067e1a
-- title:
--   Lemma 4 — elliptical potential lemma $\sum_t\|x_t\|^2_{\Sigma_{t-1}^{-1}}\le2d\log\frac{\lambda d+T}{\lambda d}$
-- statement:
--   Let $\lambda\ge1$ and let $x_1,x_2,\dots\in\mathbb R^d$ satisfy $\|x_t\|_2\le1$ for all $t\ge1$. Define $\Sigma_0=\lambda I_d$ and $\Sigma_t=\lambda I_d+\sum_{t'=1}^t x_{t'}x_{t'}^\top$ for $t\ge1$. Then for every $T\ge1$,
--
--   $$
--   \sum_{t=1}^T\|x_t\|^2_{\Sigma_{t-1}^{-1}}\ \le\ 2d\log\Big(\frac{\lambda d+T}{\lambda d}\Big),
--   $$
--
--   where $\|x\|^2_{\Sigma^{-1}}=x^\top\Sigma^{-1}x$.
--
--   In the regret analysis of UCB pricing it is applied in dimension $2d$ to the regressors $z_t$ with $\lambda=1$, which turns the sum of single-period regret bounds into a $\sqrt{T}$ rate.
--
--   **Formalization Note** The sequence is `a : ℕ → Fin d → ℝ`; $\Sigma_t$ is `BanditAlgorithm.regularizedDesignMatrix d λ a t` on the one-point sample space; the inverse is Mathlib's matrix inverse, the true inverse as $\Sigma_t$ is positive definite. Unlike the published `BanditAlgorithm.elliptical_potential_lemma`, there is no $\min(1,\cdot)$ in the sum.
--
--   Differences from the source:
--   - generalization: xₜ ∈ ℝ^d with a dimension d ≥ 1 → any d ∈ ℕ; reason: at d = 0 both sides are 0; for d ≥ 1 it is the source's statement
--   - encoding: Σₜ = λI_d + Σ_{t′≤t} x_{t′}x_{t′}ᵀ and ‖x‖²_{Σ⁻¹} → BanditAlgorithm.regularizedDesignMatrix on Unit and x ⬝ᵥ Σ⁻¹ *ᵥ x; reason: Lean convention; the same matrices and quadratic forms
-- source:
--   Wang, Talluri & Li, On Dynamic Pricing with Covariates, arXiv:2112.13254v3, Lemma 4 (Elliptical Potential Lemma, Lai and Wei 1982), p.27

import Mathlib
import Definitions.Def_SelfNormalizedProcess

open Matrix

namespace DynPricingCov

/-- **Lemma 4** (Elliptical Potential Lemma, (Lai and Wei, 1982)), Wang, Talluri & Li, On Dynamic
Pricing with Covariates, arXiv:2112.13254v3, p.27: for any constant `λ ≥ 1` and sequence
`{x_t}_{t ≥ 1}` in `ℝ^d` with `‖x_t‖₂ ≤ 1` for all `t ≥ 1`, let `Σ_0 = λ I_d` and
`Σ_t = λ I_d + Σ_{t′=1}^t x_{t′} x_{t′}ᵀ`. Then for any `T ≥ 1`,
`Σ_{t=1}^T ‖x_t‖²_{Σ_{t−1}⁻¹} ≤ 2d log((λd + T)/(λd))`.

**Formalization Note** The sequence is `a : ℕ → Fin d → ℝ` (the paper's `x_t`); `Σ_t` is the
published `BanditAlgorithm.regularizedDesignMatrix d λ a t`, on the one-point space `Unit` (the
sequence is deterministic). `‖v‖²_{Σ⁻¹} = vᵀ Σ⁻¹ v`, with Mathlib's matrix inverse (the true
inverse: `Σ_t` is positive definite for `λ ≥ 1`). -/
theorem lemma_4 {d : ℕ} {lam : ℝ} (hlam : 1 ≤ lam) (a : ℕ → Fin d → ℝ)
    (ha : ∀ t : ℕ, 1 ≤ t → Real.sqrt (a t ⬝ᵥ a t) ≤ 1) {T : ℕ} (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Icc 1 T,
        a t ⬝ᵥ (BanditAlgorithm.regularizedDesignMatrix d lam (fun s (_ : Unit) => a s)
          (t - 1) ())⁻¹ *ᵥ a t ≤
      2 * d * Real.log ((lam * d + T) / (lam * d)) := by sorry

end DynPricingCov
