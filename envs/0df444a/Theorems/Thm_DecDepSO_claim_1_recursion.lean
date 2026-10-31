-- Prove2me | Theorems.Thm_DecDepSO_claim_1_recursion
-- name    : DecDepSO.claim_1_recursion
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:25.609563+00:00
-- url     : https://prove2.me/theorems/a7d1560e-a5a0-4966-a473-e03a966082d5
-- title:
--   Theorem 7.3, proof of claim 1 — $\mathbb E\|x_{t+1}-\bar x\|^2\le\big(1-\frac{\alpha\eta(1-\rho)}{1+\eta\alpha}\big)\mathbb E\|x_t-\bar x\|^2+\frac{2\eta^2\sigma^2}{1+\eta\alpha}$
-- statement:
--   Suppose Assumption 7 holds, we are in the regime $\rho=B/\alpha<1$, and set $\hat\alpha:=\alpha-B$. Let $x_t$ be the iterates of Algorithm 1 run with a constant step $\eta$ satisfying
--   $$
--   0<\eta\le\frac{1}{B^2/\hat\alpha+L}.
--   $$
--   Then for every $t\ge0$,
--   $$
--   \mathbb E\|x_{t+1}-\bar x\|^2\ \le\ \Big(1-\frac{\alpha\eta(1-\rho)}{1+\eta\alpha}\Big)\mathbb E\|x_t-\bar x\|^2+\frac{2\eta^2\sigma^2}{1+\eta\alpha}.
--   $$
--
--   Since $\alpha\eta(1-\rho)=\eta\hat\alpha$, the squared distance to the solution contracts by the factor $1-\eta\hat\alpha/(1+\eta\alpha)<1$ up to an additive noise term of order $\eta^2\sigma^2$. Unrolling this recursion gives the estimate (7.3) of Theorem 7.3.
--
--   **Formalization Note** Only the hypotheses of Claim 1 are assumed. The paper derives the display from (7.5), whose derivation uses $\eta\le1/(2L)$; the display is nevertheless true without that condition, because $\eta\alpha\le\eta L<1$ under Claim 1's step-size bound.
--
--   Differences from the source:
--   - generalization: g_t = g(x_t), a fresh draw with ‖E[g(x)] − ∇f(x)‖ ≤ B‖x − x̄‖ and E‖g(x) − E[g(x)]‖² ≤ σ²; E_t conditions on x_0, …, x_t → the same two bounds conditionally on a filtration 𝓕_t to which x_t is adapted, with g_t 𝓕_{t+1}-measurable and square integrable; reason: a fresh draw satisfies them with 𝓕_t = σ(g_0, …, g_{t−1}), and conditioning on x_0, …, x_t is recovered by the tower property; the proof uses nothing else.
--   - encoding: x_{t+1} = prox_{η r}(x_t − η g_t) = argmin_y {r(y) + ‖y − w‖²/(2η)} → GoldenRatioVI.IsProx D (η · r) w x_{t+1}: x_{t+1} ∈ D minimizes η r(y) + ‖y − w‖²/2; reason: multiplying by η > 0 does not change the minimizers; under Assumption 7 the minimizer exists and is unique.
--   - generalization: Algorithm 1 runs for t = 0, 1, …, T → an infinite run, every t ∈ ℕ; reason: the first T + 1 steps of the infinite run are a run of Algorithm 1 up to T.
--   - encoding: Algorithm 1's input x0 → a deterministic point x₀ (IsBiasedProxSGDRun.init); reason: the input of Algorithm 1 is a point, as (7.4) and Corollary 7.4 show by using φ(x0) and ‖x0 − x̄‖² with no expectation.
--   - encoding: Rd, "a Euclidean space" (p.5) → a finite-dimensional real inner product space E; reason: every such space is isometric to some Rd and the paper calls Rd a Euclidean space.
--   - encoding: r: Rd → R ∪ {∞} closed and convex → the pair (D, r) with GoldenRatioVI.IsProperConvexLsc D r; reason: closed = lower semicontinuous extension; D ≠ ∅ is implicit because φ has a minimizer x̄ ∈ dom r.
--   - encoding: expectations E[·] of nonnegative quantities → lower Lebesgue integrals ∫⁻ ENNReal.ofReal(·) dP in [0, ∞], compared with ENNReal.ofReal of the right side; reason: same value whenever the expectation is finite, and no integrability is presupposed; the right sides are nonnegative under the hypotheses.
--   - generalization: the display is derived from (7.5), i.e. under η ≤ 1/(2L) in addition to Claim 1's step-size bound, and the sentence before it writes η < 1/(B²/α̂ + L) → only Claim 1's hypotheses ρ < 1 and 0 < η ≤ 1/(B²/α̂ + L); reason: the display is true under these alone (prox nonexpansiveness gives the factor (1 − ηα̂)² ≤ 1 − ηα̂/(1 + ηα) and noise η²σ² ≤ 2η²σ²/(1 + ηα) since ηα < 1), so dropping η ≤ 1/(2L) and allowing equality is more general.
-- source:
--   Drusvyatskiy, Xiao, Stochastic optimization with decision-dependent distributions, arXiv:2011.11173v2, Theorem 7.3, proof of claim 1, second display, p.27

import Mathlib
import Definitions.Def_DecDepSO_Assumption7ab
import Definitions.Def_DecDepSO_IsBiasedProxSGDRun

open MeasureTheory

namespace DecDepSO

/-- **Proof of Theorem 7.3, Claim 1: the contraction of `E‖x_t − x̄‖²`.**
Drusvyatskiy, Xiao, *Stochastic optimization with decision-dependent distributions*,
arXiv:2011.11173v2, proof of Theorem 7.3, proof of claim 1, second display, p.27: "The assumption
η < 1/(B²/α̂ + L) directly implies η²B²/(1 − ηL) ≤ αη(1 − ρ), and therefore we deduce
E‖xt+1 − x̄‖² ≤ (1 − αη(1 − ρ)/(1 + ηα)) E‖xt − x̄‖² + 2η²σ²/(1 + ηα)."

Under Assumption 7, in the regime `ρ = B/α < 1`, for Algorithm 1 run with a constant step
`0 < η ≤ 1/(B²/α̂ + L)`, `α̂ = α − B`, for every `t`
`E‖x_{t+1} − x̄‖² ≤ (1 − αη(1 − B/α)/(1 + ηα)) E‖x_t − x̄‖² + 2η²σ²/(1 + ηα)`.

**Formalization Note.** Only Claim 1's hypotheses are assumed (no `η ≤ 1/(2L)`): the display is
true under them (the factor is at least `(1 − ηα̂)²` and the noise term at least `η²σ²`, since
`ηα ≤ ηL < 1`). Expectations of the nonnegative quantities are lower Lebesgue integrals in
`[0, ∞]` (`∫⁻` of `ENNReal.ofReal`), so no integrability is presupposed; both coefficients on the
right are positive under the hypotheses, so `ENNReal.ofReal` does not truncate them. -/
theorem claim_1_recursion {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℕ mΩ}
    {f : E → ℝ} {D : Set E} {r : E → ℝ} {L B α σ : ℝ} {xbar : E}
    {η : ℝ} {x₀ : E} {x g : ℕ → Ω → E}
    (hA : Assumption7ab f D r L B α xbar)
    (hrun : IsBiasedProxSGDRun P 𝓕 f D r B σ xbar (fun _ => η) x₀ x g)
    (hρ : B / α < 1) (hη : η ≤ 1 / (B ^ 2 / (α - B) + L)) (t : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (‖x (t + 1) ω - xbar‖ ^ 2) ∂P ≤
      ENNReal.ofReal (1 - α * η * (1 - B / α) / (1 + η * α)) *
          ∫⁻ ω, ENNReal.ofReal (‖x t ω - xbar‖ ^ 2) ∂P
        + ENNReal.ofReal (2 * η ^ 2 * σ ^ 2 / (1 + η * α)) := by sorry

end DecDepSO
