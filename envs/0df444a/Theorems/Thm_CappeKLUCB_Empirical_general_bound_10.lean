-- Prove2me | Theorems.Thm_CappeKLUCB_Empirical_general_bound_10
-- name    : CappeKLUCB.Empirical.general_bound_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:08:35.43526+00:00
-- url     : https://prove2.me/theorems/1c4279d7-193b-463f-b364-7b25bc416bf7
-- title:
--   (9)–(10), p. 10 — 𝔼[N_a(T)] ≤ f(T)/𝒦_inf(ν_a, μ⋆) + Σ_{n>n₀} ℙ{ν̂_{a,n} ∈ 𝒞} + Σ_t ℙ{μ† ≥ U_{a⋆}(t)} + 2 for Algorithm 3
-- statement:
--   Consider a stochastic bandit with $K\ge2$ arms whose reward distributions $\nu_1,\dots,\nu_K$ belong to $\mathcal F$, with means $\mu_a$ and $\mu^\star=\max_a\mu_a$, and a run of Algorithm 3 with $f(t)=\log t+\log\log t$. Let $a^\star$ be an optimal arm, $a$ a suboptimal arm ($\mu_a<\mu^\star$), $\mu^\dagger\in\mathbb R$ and $T\ge3$. With
--   $$n_0 = \Bigl\lceil \frac{f(T)}{\mathcal K_{\inf}(\nu_a,\mu^\star)}\Bigr\rceil \qquad (9)$$
--   one has
--   $$\mathbb E[N_a(T)] \le \frac{f(T)}{\mathcal K_{\inf}(\nu_a,\mu^\star)} + \sum_{n=n_0+1}^{T-K}\mathbb P\bigl\{\hat\nu_{a,n}\in\mathcal C_{\mu^\dagger,f(T)/n}\bigr\} + \sum_{t=K}^{T-1}\mathbb P\bigl\{\mu^\dagger\ge U_{a^\star}(t)\bigr\} + 2. \qquad (10)$$
--
--   This is the general bound of which Theorem 2 is an instance: the leading term $f(T)/\mathcal K_{\inf}(\nu_a,\mu^\star)\approx\log T/\mathcal K_{\inf}(\nu_a,\mu^\star)$ matches the Burnetas–Katehakis lower bound, and the two sums are the quantities that the case-specific arguments show to be $o(\log T)$.
--
--   **Formalization Note** The page writes the first sum over all $n\ge n_0+1$; the terms with $n>T-K$ do not arise from (8), so the sum is stated over $n_0+1\le n\le T-K$, which implies the printed form and avoids an infinite series of probabilities. $\mathcal K_{\inf}$ is converted to a real number: for $\nu_a\in\mathcal F$ with $\mu_a<\mu^\star$ it is positive, and it is finite when $\mu^\star<1$; if $\mu^\star=1$ it is $+\infty$, Lean's conversion gives $0$ and division by $0$ gives $0$, which coincides with the convention $f(T)/(+\infty)=0$, so no hypothesis $\mu^\star<1$ is needed. Representation as for (8): reward stacks, pathwise $[0,1]$ rewards, measurable arm choices, outer probabilities. $\lceil\cdot\rceil$ is the natural-number ceiling.
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, p. 10, (9) and (10), for Algorithm 3 of p. 15 with f of Theorem 2

import Mathlib
import Definitions.Def_CappeKLUCB_Empirical_Setting

namespace CappeKLUCB.Empirical

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
open scoped ENNReal

/-- The general bound (10), with `n₀ = ⌈f(T)/𝒦_inf(ν_a, μ⋆)⌉` of (9), Cappé et al.,
arXiv:1210.1136v4, p. 10, for Algorithm 3 (p. 15) with `f(t) = log t + log log t`; the sum over
`n ≥ n₀ + 1` is the finite sum over `n₀ + 1 ≤ n ≤ T − K` produced by (8). -/
theorem general_bound_10 {K : ℕ} (hK : 2 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (hF : ∀ a, IsFinSupp01 (P.map (X a 0))) (hbdd : ∀ a k ω, X a k ω ∈ Set.Icc (0 : ℝ) 1)
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t)) (hrun : IsEmpKLUCBRun f₂ X I)
    (a astar : Fin K) (hastar : μ astar = bestMean μ) (ha : μ a < bestMean μ)
    (μdag : ℝ) (T : ℕ) (hT : 3 ≤ T) :
    ∫ ω, (pullCount I a T ω : ℝ) ∂P ≤
      f₂ T / (Kinf (P.map (X a 0)) (bestMean μ)).toReal
        + ∑ n ∈ Finset.Icc (⌈f₂ T / (Kinf (P.map (X a 0)) (bestMean μ)).toReal⌉₊ + 1) (T - K),
            P.real {ω | InC μdag (f₂ T / (n : ℝ)) (empMeasure (fun k => X a k ω) n)}
        + ∑ t ∈ Finset.Ico K T, P.real {ω | μdag ≥ index f₂ X I astar t ω}
        + 2 := by sorry

end CappeKLUCB.Empirical
