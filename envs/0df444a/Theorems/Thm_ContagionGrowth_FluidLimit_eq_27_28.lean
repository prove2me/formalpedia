-- Prove2me | Theorems.Thm_ContagionGrowth_FluidLimit_eq_27_28
-- name    : ContagionGrowth.FluidLimit.eq_27_28
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:31.009979+00:00
-- url     : https://prove2.me/theorems/9b9ffafd-7e40-40d5-ab70-4d2bb0d51f35
-- title:
--   (27)–(28), proof of Theorem 5, p. 26 — the k-th interaction time T_k with Exp(n) gaps converges in probability to γλ̄
-- statement:
--   Let $\bar\lambda^{(n)}\to\bar\lambda\in(0,\infty)$, let $\gamma\in[0,1]$, and let $k_n\in\mathbb N$ satisfy $k_n=\gamma\bar\lambda^{(n)}n+o(n)$. For each $n$ let $\Delta_1,\dots,\Delta_{k_n}$ be i.i.d. exponential random variables with rate $n$ (mean $1/n$), and $T^{(n)}_{k_n}=\Delta_1+\dots+\Delta_{k_n}$ the calendar time of the $k_n$-th interaction. Then
--   $$T^{(n)}_{k_n}\xrightarrow{\ p\ }\gamma\bar\lambda,$$
--   that is, for every $\varepsilon>0$, $\mathbb P\big(|T^{(n)}_{k_n}-\gamma\bar\lambda|>\varepsilon\big)\to0$ as $n\to\infty$.
--
--   The paper derives it from $\mathbb E(T^{(n)}_{k})=k/n$ (27) and $\mathrm{Var}(T^{(n)}_{k})=k/n^2$ (28). It converts interaction counts into calendar time, which is what turns the growth of thresholds into the growth times $\hat t_{\lambda,\theta,\ell}$.
--
--   **Formalization Note.** For each $n$ the gaps live on their own probability space, the product of $k_n$ copies of $\mathrm{Exp}(n)$; convergence in probability is stated in the explicit $\forall\varepsilon$ form. $o(n)$ is encoded as $(k_n-\gamma\bar\lambda^{(n)}n)/n\to0$.
-- source:
--   Amini, Minca & Sulem, A dynamic contagion risk model with recovery features, preprint (February 2021), p. 26, (27)–(28), proof of Theorem 5, §4.3

import Mathlib

namespace ContagionGrowth.FluidLimit

open Filter Topology MeasureTheory

/-- (27)–(28), proof of Theorem 5, §4.3, p. 26: if `λ̄⁽ⁿ⁾ → λ̄ ∈ (0, ∞)` and
`k_n = γ λ̄⁽ⁿ⁾ n + o(n)` with `γ ∈ [0, 1]`, then the calendar time
`T⁽ⁿ⁾_{k_n} = Δ_1 + ⋯ + Δ_{k_n}` of the `k_n`-th interaction, with i.i.d. `Exp(n)` gaps,
converges in probability to `γ λ̄`. -/
theorem eq_27_28 (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (lbarN : ℕ → ℝ) (lb : ℝ) (hlb : 0 < lb)
    (hlbN : Tendsto lbarN atTop (𝓝 lb)) (k : ℕ → ℕ)
    (hk : Tendsto (fun n : ℕ => ((k n : ℝ) - γ * lbarN n * n) / n) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n : ℕ =>
      (Measure.pi fun _ : Fin (k n) => ProbabilityTheory.expMeasure (n : ℝ))
        {Δ : Fin (k n) → ℝ | ε < |∑ i, Δ i - γ * lb|}) atTop (𝓝 0) := by sorry

end ContagionGrowth.FluidLimit
