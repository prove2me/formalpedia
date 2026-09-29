-- Prove2me | Theorems.Thm_FirstOrderOpt_Stochastic_martingale_difference_deviation_bound
-- name    : FirstOrderOpt.Stochastic.martingale_difference_deviation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:00:06.202715+00:00
-- url     : https://prove2.me/theorems/87af245d-5973-4fb4-a5c7-f68c8db80ab3
-- title:
--   Lemma 4.1 — martingale-difference deviation bound
-- statement:
--   Let $\xi_{[t]} \equiv \{\xi_1,\dots,\xi_t\}$ be a sequence of iid random variables generating a
--   filtration $(\mathcal F_t)_{t\ge0}$, and let $\zeta_t = \zeta_t(\xi_{[t]})$ be deterministic
--   Borel functions of $\xi_{[t]}$ (i.e. $\mathcal F_t$-measurable) such that
--   $\mathbb E_{|\xi_{[t-1]}}[\zeta_t] = 0$ a.s. and $\mathbb E_{|\xi_{[t-1]}}[\exp\{\zeta_t^2/
--   \sigma_t^2\}] \le \exp\{1\}$ a.s., where $\sigma_t > 0$ are deterministic constants.
--
--   **Lemma 4.1.** For every $\lambda \ge 0$,
--   $$\mathrm{Prob}\Big\{\sum_{t=1}^N \zeta_t > \lambda\sqrt{\sum_{t=1}^N \sigma_t^2}\Big\} \le
--   \exp\{-\lambda^2/3\}.$$
--
--   This is the chapter's core probabilistic tool: a Chernoff-type concentration bound for a
--   conditionally sub-Gaussian martingale-difference sequence, proved via a bound on the
--   conditional moment-generating function and Chebyshev's inequality applied to
--   $\exp\{\nu\sum_t\zeta_t\}$. It supplies the large-deviation half of the chapter's results
--   (`Proposition 4.1` and `Theorem 4.2(b)`, not formalized in this mission — see *Formalization
--   scope*) exactly as the plain second-moment bound $\mathbb E[\|G_t-g(x_t)\|_*^2]\le\sigma^2$
--   supplies the goal theorem's expected-value bound.
--
--   **Formalization Note.** $\xi_{[t]}$'s generated filtration is modeled directly as a Mathlib
--   `MeasureTheory.Filtration ℕ` on the ambient measurable space, and "$\zeta_t$ is a deterministic
--   Borel function of $\xi_{[t]}$" as $\mathcal F_t$-measurability of $\zeta_t$. The conditional
--   expectation and conditional-a.s. bounds use Mathlib's `condExp` (notation `μ[· | 𝓕 (t-1)]`);
--   the conclusion's probability is stated as `(μ {ω | …}).toReal ≤ Real.exp (-(λ^2)/3)`, converting
--   the `ENNReal`-valued measure of the deviation event to a real number, which is legitimate
--   since `μ` is a probability measure. The strict inequality in the deviation event matches the
--   book's own `>` (not `≥`).
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 114, Lemma 4.1

import Mathlib

namespace FirstOrderOpt.Stochastic

open MeasureTheory

/-- Lemma 4.1 (martingale-difference deviation bound). `𝓕` is a filtration of the ambient
`MeasurableSpace Ω` (formalizing `ξ[t] ≡ {ξ1,…,ξt}`); `ζ t` is `𝓕 t`-measurable ("a deterministic
Borel function of `ξ[t]`"); `σ t > 0` are deterministic constants. If for every `t ≥ 1` the
conditional expectation of `ζ t` given the past `𝓕 (t-1)` is a.e. zero, and the conditional
expectation of `exp{ζ t ^ 2 / σ t ^ 2}` given `𝓕 (t-1)` is a.e. at most `exp 1`, then for every
`N ≥ 1` and `λ ≥ 0`, `Prob{Σ_{t=1}^N ζ t > λ√(Σ_{t=1}^N σt²)} ≤ exp{-λ²/3}`.

**Formalization Note.** The probability is expressed via `(μ {ω | …}).toReal`, which is
Mathlib's standard route from an `ENNReal`-valued measure to a real inequality against
`Real.exp (-(λ^2)/3)`, since `μ` is a probability measure (`IsProbabilityMeasure μ`) and every
event measure here is finite. `hintmean`/`hinttail` guard `hmean`/`htail`'s conditional-expectation
claims with `Integrable`: Mathlib sets `condExp` of a non-integrable function to `0`
(`condExp_of_not_integrable`), so without these guards a heavy-tailed `ζ t` with non-integrable
`exp{ζt²/σt²}` would satisfy `hmean`/`htail` vacuously while violating the book's genuine
Chernoff-type tail decay. -/
theorem martingale_difference_deviation_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (𝓕 : Filtration ℕ mΩ) (ζ : ℕ → Ω → ℝ) (σ : ℕ → ℝ)
    (hσ : ∀ t, 0 < σ t)
    (hadapt : ∀ t, Measurable[𝓕 t] (ζ t))
    (hintmean : ∀ t, 1 ≤ t → Integrable (ζ t) μ)
    (hinttail : ∀ t, 1 ≤ t → Integrable (fun ω => Real.exp ((ζ t ω) ^ 2 / (σ t) ^ 2)) μ)
    (hmean : ∀ t, 1 ≤ t → (μ[ζ t | 𝓕 (t - 1)]) =ᵐ[μ] 0)
    (htail : ∀ t, 1 ≤ t →
      (μ[(fun ω => Real.exp ((ζ t ω) ^ 2 / (σ t) ^ 2)) | 𝓕 (t - 1)])
        ≤ᵐ[μ] (fun _ => Real.exp 1))
    (N : ℕ) (hN : 1 ≤ N) (lam : ℝ) (hlam : 0 ≤ lam) :
    (μ {ω | lam * Real.sqrt (∑ t ∈ Finset.Icc 1 N, (σ t) ^ 2) < ∑ t ∈ Finset.Icc 1 N, ζ t ω}).toReal
      ≤ Real.exp (-(lam ^ 2) / 3) := by sorry

end FirstOrderOpt.Stochastic
