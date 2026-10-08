-- Prove2me | Theorems.Thm_CappeKLUCB_ExpFam_general_bound_10
-- name    : CappeKLUCB.ExpFam.general_bound_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:20:33.134216+00:00
-- url     : https://prove2.me/theorems/cd6598b7-823d-488f-9453-71e23625503c
-- title:
--   (10), with n₀ of (9), p. 10 — 𝔼[Nₐ(T)] ≤ f(T)/d(μₐ, μ⋆) + Σ_{n>n₀} ℙ{…} + Σₜ ℙ{μ† ≥ U_{a⋆}(t)} + 2
-- statement:
--   In the setting of Theorem 1 (arms in a canonical regular exponential family indexed by its natural parameter space, a run of Algorithm 2 with $f = f_1$ and measurable arm choices), let $a^\star$ be an optimal arm, $a$ a suboptimal arm ($\mu_a<\mu^\star$), $\mu^\dagger\in\mathbb R$ and $T\in\mathbb N$ (any horizon, as on the page). Let
--   $$n_0 = \Bigl\lceil \frac{f(T)}{d(\mu_a,\mu^\star)}\Bigr\rceil. \tag{9}$$
--   Then
--   $$\mathbb E[N_a(T)] \le \frac{f(T)}{d(\mu_a,\mu^\star)} + \sum_{n=n_0+1}^{T-K}\mathbb P\bigl\{\mu^\dagger < \mathrm{klIndex}(\hat\mu_{a,n}, f(T)/n)\bigr\} + \sum_{t=K}^{T-1}\mathbb P\{\mu^\dagger \ge U_{a^\star}(t)\} + 2.$$
--
--   This is the general bound of §3.1 in the exponential-family model: the leading term $f(T)/d(\mu_a,\mu^\star)$ is the Lai–Robbins rate, and the two sums are the quantities that Facts 1 and 2 of the paper declare negligible with respect to $\log T$.
--
--   **Formalization Note** In this model $\mathcal K_{\inf}(\nu_a,\mu^\star) = d(\mu_a,\mu^\star)$ (§4.2, p. 14), so the paper's $\mathcal K_{\inf}$ is written as $d$. The paper writes the middle sum over all $n\ge n_0+1$; the inequality chain (8) only produces $n\le T-K$, and the finite sum is stated (it implies the printed form, whose extra terms are nonnegative). Probabilities of index events are outer measures.
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, p. 10, (9) and (10)

import Mathlib
import Definitions.Def_CappeKLUCB_ExpFam_Setting

namespace CappeKLUCB.ExpFam

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
  OptimalBAI.OptProportions

/-- (10), with `n₀` of (9), Cappé et al., arXiv:1210.1136v4, p. 10. -/
theorem general_bound_10 {K : ℕ} (hK : 2 ≤ K) (F : ExpFamily) (hnat : IsNatural F)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hrun : IsKLUCBRun F f₁ X I) (a astar : Fin K) (hastar : μ astar = bestMean μ)
    (ha : μ a < bestMean μ) (μdag : ℝ) (T : ℕ) :
    ∫ ω, (pullCount I a T ω : ℝ) ∂P ≤
      f₁ T / F.d (μ a) (bestMean μ)
        + ∑ n ∈ Finset.Icc (⌈f₁ T / F.d (μ a) (bestMean μ)⌉₊ + 1) (T - K),
            P.real {ω | μdag < klIndex F (sampleMean X a n ω) (f₁ T / (n : ℝ))}
        + ∑ t ∈ Finset.Ico K T, P.real {ω | klucbIndex F f₁ X I astar t ω ≤ μdag}
        + 2 := by sorry

end CappeKLUCB.ExpFam
