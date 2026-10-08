-- Prove2me | Theorems.Thm_BastaniBayati_LassoBandit_lasso_tail_inequality_adapted
-- name    : BastaniBayati.LassoBandit.lasso_tail_inequality_adapted
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T09:11:29.996186+00:00
-- url     : https://prove2.me/theorems/43cc2cf8-b3c2-449f-86c1-542cab33e319
-- title:
--   LASSO tail inequality for adapted observations
-- statement:
--   Consider a linear model $Y=\mathbf X\beta+\varepsilon$ with $n\ge1$ rows $X_1,\dots,X_n\in\mathbb R^d$ observed sequentially on a filtered probability space $(\mathcal F_t)$: each row $X_t$ is $\mathcal F_{t-1}$-measurable, so it may depend on the past rows and responses $\{X_{t'},Y(t')\}_{t'<t}$; each noise $\varepsilon_t$ is $\mathcal F_t$-measurable and $\sigma$-subgaussian conditionally on $\mathcal F_{t-1}$, i.e. $\mathbb E[e^{s\varepsilon_t}\mid\mathcal F_{t-1}]\le e^{\sigma^2s^2/2}$ for all $s\in\mathbb R$ ($\sigma>0$). Assume every realization satisfies $\|X_t\|_\infty\le x_{\max}$ ($x_{\max}>0$), and $\|\beta\|_0=s_0\ge1$.
--
--   Then for any $\phi>0$ and $\chi>0$, every LASSO estimator $\hat\beta_{\mathbf X,Y}(\lambda)$ with $\lambda=\chi\phi^2/(4s_0)$ satisfies
--   $$\Pr\big[\|\hat\beta_{\mathbf X,Y}(\lambda)-\beta\|_1>\chi\big]\le 2\exp\big[-C_1(\phi)n\chi^2+\log d\big]+\Pr\big[\hat\Sigma(\mathbf X)\notin\mathcal C(\mathrm{supp}(\beta),\phi)\big],$$
--   where $C_1(\phi)=\phi^4/(512s_0^2\sigma^2x_{\max}^2)$ and $\hat\Sigma(\mathbf X)=\mathbf X^\top\mathbf X/n$.
--
--   This is Proposition 1 of Bastani and Bayati: a LASSO oracle inequality that does not need i.i.d. rows, which is what allows the all-sample estimators of the LASSO Bandit, trained on adaptively collected data, to be analysed.
--
--   **Formalization Note** Rows are indexed $0,\dots,n-1$, with row $t$ measurable for $\mathcal F_t$ and noise $t$ measurable for $\mathcal F_{t+1}$ and conditionally subgaussian given $\mathcal F_t$. The conditionally subgaussian noise is the version the paper says it proves (paragraph after Remark 6); $n\ge1$, $s_0\ge1$, $\sigma>0$, $x_{\max}>0$ are made explicit. The estimator is an arbitrary minimizer for each outcome; probabilities of possibly non-measurable events are outer measures.
-- source:
--   Bastani & Bayati, Online Decision Making with High-Dimensional Covariates, Operations Research 68(1):276–294 (2020), doi:10.1287/opre.2019.1902, p. 283, Proposition 1 (setting of §3.2 and the paragraph after Remark 6, pp. 283–284)

import Mathlib
import Definitions.Def_BastaniBayati_LassoBandit_Basic
import Definitions.Def_BastaniBayati_LassoBandit_Constants

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace BastaniBayati.LassoBandit

/-- **Proposition 1** (LASSO Tail Inequality for Adapted Observations), Bastani–Bayati, p. 283.
Rows `X₀, …, X_{n−1}` (the paper's `X₁, …, Xₙ`) and noises `ε₀, …, ε_{n−1}` on a filtered
probability space: `X_t` is `ℱ_t`-measurable (it may depend on the past rows and responses),
`ε_t` is `ℱ_{t+1}`-measurable and `σ`-subgaussian conditionally on `ℱ_t`, the responses are
`Y(t) = X_tᵀβ + ε_t`, `‖β‖₀ = s₀ ≥ 1`, every realization has `‖X_t‖_∞ ≤ x_max`. Then for every
`φ, χ > 0`, every LASSO estimator `β̂` with `λ = χφ²/(4s₀)` satisfies
`Pr[‖β̂ − β‖₁ > χ] ≤ 2 exp[−C₁(φ) n χ² + log d] + Pr[Σ̂(X) ∉ 𝒞(supp(β), φ)]`. -/
theorem lasso_tail_inequality_adapted {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d n : ℕ} (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → Fin d → ℝ)
    (ε : ℕ → Ω → ℝ) (β : Fin d → ℝ) (σ : ℝ≥0) (xmax : ℝ) (s0 : ℕ) (φ χ : ℝ)
    (βhat : Ω → Fin d → ℝ)
    (hn : 1 ≤ n) (hσ : 0 < σ) (hxmax : 0 < xmax)
    (hs0 : (supp β).card = s0) (hs0pos : 1 ≤ s0) (hφ : 0 < φ) (hχ : 0 < χ)
    (hX_adapted : ∀ t < n, Measurable[ℱ t] (X t))
    (hε_meas : ∀ t < n, Measurable[ℱ (t + 1)] (ε t))
    (hε_int : ∀ t < n, ∀ s : ℝ, Integrable (fun ω => Real.exp (s * ε t ω)) P)
    (hε_subg : ∀ t < n, ∀ s : ℝ,
      P[fun ω => Real.exp (s * ε t ω) | ℱ t] ≤ᵐ[P] fun _ => Real.exp ((σ : ℝ) ^ 2 * s ^ 2 / 2))
    (hbound : ∀ t < n, ∀ ω, ‖X t ω‖ ≤ xmax)
    (hβhat : ∀ ω, IsLassoMinimizer (fun k : Fin n => X k ω) (fun k : Fin n => X k ω ⬝ᵥ β + ε k ω)
      (χ * φ ^ 2 / (4 * s0)) (βhat ω)) :
    P {ω | χ < l1Norm (βhat ω - β)} ≤
      ENNReal.ofReal (2 * Real.exp (-(C1 s0 σ xmax φ) * n * χ ^ 2 + Real.log d)) +
        P {ω | sampleCov (fun k : Fin n => X k ω) ∉ compatSet (supp β) φ} := by sorry

end BastaniBayati.LassoBandit
