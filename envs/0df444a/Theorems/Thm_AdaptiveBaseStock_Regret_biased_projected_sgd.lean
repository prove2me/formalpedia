-- Prove2me | Theorems.Thm_AdaptiveBaseStock_Regret_biased_projected_sgd
-- name    : AdaptiveBaseStock.Regret.biased_projected_sgd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:25:11.217329+00:00
-- url     : https://prove2.me/theorems/17b8fb2b-8d18-40f3-bd7b-8d41e0ce9b7d
-- title:
--   Theorem 11 — projected stochastic gradient descent with biased gradients on an interval
-- statement:
--   Let $\mathcal S = [m, M]$ with $m \le M$, and let $\Phi$ be convex on $\mathcal S$ with derivative $\Phi'$ (one-sided at the endpoints) and a minimizer $z^* \in \mathcal S$. On a filtered probability space $(\mathcal F_t)_{t\ge1}$, let $Z_1 \in \mathcal S$ and
--   $$Z_{t+1} = P_{\mathcal S}\big(Z_t - \epsilon_t H_t\big), \qquad \epsilon_t = \frac{\zeta\, \mathrm{diam}(\mathcal S)}{\overline B}\cdot \frac1{t^\alpha},$$
--   where $\zeta > 0$, $\alpha \in (0,1)$, $\overline B > 0$, $Z_t$ is $\mathcal F_t$-measurable, the estimate $H_t$ is $\mathcal F_{t+1}$-measurable with $E[H_t^2] \le \overline B^2$, and $P_{\mathcal S}(z) = \max\{m, \min\{z, M\}\}$. Let $\eta_t = E[H_t \mid \mathcal F_t] - \Phi'(Z_t)$ be the bias of the estimate. Then for all $T \ge 1$,
--   $$\sum_{t=1}^T E\big[\Phi(Z_t) - \Phi(z^*)\big] \le \mathrm{diam}(\mathcal S)\Big\{\overline B\Big[\frac{T^\alpha}{2\zeta} + \frac{\zeta\, T^{1-\alpha}}{2(1-\alpha)}\Big] + \sum_{t=1}^T E|\eta_t|\Big\}.$$
--
--   This is the online convex optimization bound that the base-stock levels $S_k$ of the algorithm obey; the bias terms are where the Markov chain enters.
--
--   **Formalization Note** The paper states the result for a compact set in $\mathbb R^n$ and writes the bias as $E[H_t(z)\mid z] - \nabla\Phi(z)$; here $\mathcal S$ is an interval (the paper's only use is $[\underline M, \overline M]$) and the bias is the conditional expectation given the history $\mathcal F_t$, which is how the paper applies it when the estimate depends on the past inventory. The second-moment bound is required unconditionally. Lean index $t$ is the paper's $t+1$.
-- source:
--   Huh, Janakiraman, Muckstadt, Rusmevichientong, An Adaptive Algorithm for Finding the Optimal Base-Stock Policy in Lost Sales Inventory Systems with Censored Demand, working paper, February 8, 2007 (published version: Math. Oper. Res., 2009, DOI 10.1287/moor.1080.0367), Theorem 11, pp. 24–25 (citing Huh and Rusmevichientong 2006a)

import Mathlib

namespace AdaptiveBaseStock.Regret

open MeasureTheory ProbabilityTheory

/-- Theorem 11, pp. 24–25 (one-dimensional, filtration form): projected stochastic gradient
descent on `𝒮 = [m, M]` with step `ϵ_t = ζ diam(𝒮) / (B̄ t^α)` and gradient estimates of second
moment at most `B̄²` satisfies
`Σ_{t=1}^T E[Φ(Z_t) - Φ(z*)] ≤ diam(𝒮) {B̄ [T^α/(2ζ) + ζ T^{1-α}/(2(1-α))] + Σ_{t=1}^T E|η_t|}`,
where `η_t = E[H_t | 𝓕_t] - Φ'(Z_t)` is the bias of the estimate. Lean index `t` is the paper's
`t + 1`. -/
theorem biased_projected_sgd {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (m M : ℝ) (hmM : m ≤ M) (Φ Φ' : ℝ → ℝ)
    (hconv : ConvexOn ℝ (Set.Icc m M) Φ)
    (hderiv : ∀ z ∈ Set.Icc m M, HasDerivWithinAt Φ (Φ' z) (Set.Icc m M) z)
    (zstar : ℝ) (hzstar : zstar ∈ Set.Icc m M) (hmin : IsMinOn Φ (Set.Icc m M) zstar)
    (Bbar ζ α : ℝ) (hB : 0 < Bbar) (hζ : 0 < ζ) (hα0 : 0 < α) (hα1 : α < 1)
    (Z H : ℕ → Ω → ℝ)
    (hZ0 : ∀ ω, Z 0 ω ∈ Set.Icc m M)
    (hZadapt : ∀ t, StronglyMeasurable[ℱ t] (Z t))
    (hHmeas : ∀ t, StronglyMeasurable[ℱ (t + 1)] (H t))
    (hH2 : ∀ t, MemLp (H t) 2 P)
    (hHbound : ∀ t, ∫ ω, H t ω ^ 2 ∂P ≤ Bbar ^ 2)
    (hrec : ∀ t ω, Z (t + 1) ω =
      max m (min (Z t ω - ζ * (M - m) / (Bbar * ((t : ℝ) + 1) ^ α) * H t ω) M))
    (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.range T, ∫ ω, (Φ (Z t ω) - Φ zstar) ∂P
      ≤ (M - m) * (Bbar * ((T : ℝ) ^ α / (2 * ζ) + ζ * (T : ℝ) ^ (1 - α) / (2 * (1 - α)))
          + ∑ t ∈ Finset.range T, ∫ ω, |P[H t | ℱ t] ω - Φ' (Z t ω)| ∂P) := by sorry

end AdaptiveBaseStock.Regret
