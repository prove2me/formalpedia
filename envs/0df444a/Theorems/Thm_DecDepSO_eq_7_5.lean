-- Prove2me | Theorems.Thm_DecDepSO_eq_7_5
-- name    : DecDepSO.eq_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:10.03201+00:00
-- url     : https://prove2.me/theorems/70c6277a-b902-4fe9-9da0-cecaa6ff775a
-- title:
--   Theorem 7.3, proof, (7.5) — one-step improvement in expectation for a constant step $\eta\le\frac1{2L}$
-- statement:
--   Suppose Assumption 7 holds (with $\rho=B/\alpha$) and let $x_t$ be the iterates of Algorithm 1 run with a constant step $\eta$ satisfying
--   $$
--   0<\eta\le\frac1{2L}.
--   $$
--   Then for every $t\ge0$ the random variables $\varphi(x_{t+1})-\varphi(\bar x)$, $\|x_t-\bar x\|^2$ and $\|x_{t+1}-\bar x\|^2$ are integrable, and
--   $$
--   2\eta\,\mathbb E[\varphi(x_{t+1})-\varphi(\bar x)]\ \le\ \Big(1-\alpha\eta(1-2\rho)+\frac{\eta^2B^2}{1-\eta L}\Big)\mathbb E\|x_t-\bar x\|^2-\mathbb E\|x_{t+1}-\bar x\|^2+2\eta^2\sigma^2. \tag{7.5}
--   $$
--
--   This is the unconditional, constant-step form of Lemma 7.2 from which both claims of Theorem 7.3 are derived: Claim 1 by bounding $\varphi(x_{t+1})-\varphi(\bar x)$ below by $\frac\alpha2\|x_{t+1}-\bar x\|^2$, Claim 2 through the averaging Corollary A.3.
--
--   **Formalization Note** Expectations are Bochner integrals; their integrability is proved as part of the conclusion, not assumed, so Lean's default value $0$ for non-integrable functions cannot satisfy the inequality.
--
--   Differences from the source:
--   - generalization: g_t = g(x_t), a fresh draw with ‖E[g(x)] − ∇f(x)‖ ≤ B‖x − x̄‖ and E‖g(x) − E[g(x)]‖² ≤ σ²; E_t conditions on x_0, …, x_t → the same two bounds conditionally on a filtration 𝓕_t to which x_t is adapted, with g_t 𝓕_{t+1}-measurable and square integrable; reason: a fresh draw satisfies them with 𝓕_t = σ(g_0, …, g_{t−1}), and conditioning on x_0, …, x_t is recovered by the tower property; the proof uses nothing else.
--   - encoding: x_{t+1} = prox_{η r}(x_t − η g_t) = argmin_y {r(y) + ‖y − w‖²/(2η)} → GoldenRatioVI.IsProx D (η · r) w x_{t+1}: x_{t+1} ∈ D minimizes η r(y) + ‖y − w‖²/2; reason: multiplying by η > 0 does not change the minimizers; under Assumption 7 the minimizer exists and is unique.
--   - generalization: Algorithm 1 runs for t = 0, 1, …, T → an infinite run, every t ∈ ℕ; reason: the first T + 1 steps of the infinite run are a run of Algorithm 1 up to T.
--   - encoding: Algorithm 1's input x0 → a deterministic point x₀ (IsBiasedProxSGDRun.init); reason: the input of Algorithm 1 is a point, as (7.4) and Corollary 7.4 show by using φ(x0) and ‖x0 − x̄‖² with no expectation.
--   - encoding: Rd, "a Euclidean space" (p.5) → a finite-dimensional real inner product space E; reason: every such space is isometric to some Rd and the paper calls Rd a Euclidean space.
--   - encoding: r: Rd → R ∪ {∞} closed and convex → the pair (D, r) with GoldenRatioVI.IsProperConvexLsc D r; reason: closed = lower semicontinuous extension; D ≠ ∅ is implicit because φ has a minimizer x̄ ∈ dom r.
--   - generalization: the expectations in (7.5) are presupposed to exist → the conclusion also asserts that the three random variables are integrable; reason: a stronger conclusion: the inequality cannot hold by Lean's default value 0 for non-integrable functions.
-- source:
--   Drusvyatskiy, Xiao, Stochastic optimization with decision-dependent distributions, arXiv:2011.11173v2, Theorem 7.3, proof, display (7.5), p.27

import Mathlib
import Definitions.Def_DecDepSO_Assumption7ab
import Definitions.Def_DecDepSO_IsBiasedProxSGDRun

open MeasureTheory

namespace DecDepSO

/-- **Display (7.5): the one-step improvement with a constant step `η ≤ 1/(2L)`.**
Drusvyatskiy, Xiao, *Stochastic optimization with decision-dependent distributions*,
arXiv:2011.11173v2, proof of Theorem 7.3, p.27: "Observe first that the assumption η ≤ 1/(2L)
implies η²σ²/(1 − ηL) ≤ 2η²σ². Therefore Lemma 7.2 yields the one step improvement:
2ηE[φ(xt+1) − φ(x̄)] ≤ (1 − αη(1 − 2ρ) + η²B²/(1 − ηL)) E‖xt − x̄‖² − E‖xt+1 − x̄‖² + 2η²σ². (7.5)"

Under Assumption 7, for Algorithm 1 run with a constant step `0 < η ≤ 1/(2L)`, for every `t` the
random variables `φ(x_{t+1}) − φ(x̄)`, `‖x_t − x̄‖²`, `‖x_{t+1} − x̄‖²` are integrable and
`2η E[φ(x_{t+1}) − φ(x̄)] ≤ (1 − αη(1 − 2B/α) + η²B²/(1 − ηL)) E‖x_t − x̄‖² − E‖x_{t+1} − x̄‖²
 + 2η²σ²`.

**Formalization Note.** Expectations are Bochner integrals; their integrability is part of the
conclusion (not assumed), so the inequality is not satisfied by Lean's junk value `0`. -/
theorem eq_7_5 {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℕ mΩ}
    {f : E → ℝ} {D : Set E} {r : E → ℝ} {L B α σ : ℝ} {xbar : E}
    {η : ℝ} {x₀ : E} {x g : ℕ → Ω → E}
    (hA : Assumption7ab f D r L B α xbar)
    (hrun : IsBiasedProxSGDRun P 𝓕 f D r B σ xbar (fun _ => η) x₀ x g)
    (hη : η ≤ 1 / (2 * L)) (t : ℕ) :
    Integrable (fun ω => (f (x (t + 1) ω) + r (x (t + 1) ω)) - (f xbar + r xbar)) P ∧
    Integrable (fun ω => ‖x t ω - xbar‖ ^ 2) P ∧
    Integrable (fun ω => ‖x (t + 1) ω - xbar‖ ^ 2) P ∧
    2 * η * ∫ ω, ((f (x (t + 1) ω) + r (x (t + 1) ω)) - (f xbar + r xbar)) ∂P ≤
      (1 - α * η * (1 - 2 * (B / α)) + η ^ 2 * B ^ 2 / (1 - η * L)) *
          ∫ ω, ‖x t ω - xbar‖ ^ 2 ∂P
        - ∫ ω, ‖x (t + 1) ω - xbar‖ ^ 2 ∂P + 2 * η ^ 2 * σ ^ 2 := by sorry

end DecDepSO
