-- Prove2me | Theorems.Thm_DecDepSO_theorem_7_3_constant_step
-- name    : DecDepSO.theorem_7_3_constant_step
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:41.45026+00:00
-- url     : https://prove2.me/theorems/b73e4dbd-74da-408f-8b65-16bbe6c90723
-- title:
--   Theorem 7.3 (Constant step size) — linear convergence of proximal SGD with bias $\le B\|x-\bar x\|$: distance for $\rho<1$, function value of the average for $\rho<\frac12$
-- statement:
--   Suppose Assumption 7 holds: $f$ is $\alpha$-strongly convex and differentiable with $L$-Lipschitz gradient, $r$ is proper, closed and convex, $\bar x$ minimizes $\varphi=f+r$, $L,B,\alpha>0$, $\rho=B/\alpha$, and the stochastic gradients have bias at most $B\|x-\bar x\|$ and variance at most $\sigma^2$. Let $x_t$ be the iterates of Algorithm 1,
--   $$
--   x_{t+1}=\mathrm{prox}_{\eta r}(x_t-\eta g_t),
--   $$
--   started at $x_0$ with a fixed step $\eta>0$. Then:
--
--   1. If $\rho<1$, set $\hat\alpha:=\alpha-B$. If $\eta\le\dfrac{1}{B^2/\hat\alpha+L}$, then for every $t\ge0$
--   $$
--   \mathbb E\|x_t-\bar x\|^2\le\Big(1-\frac{2\eta\hat\alpha}{3}\Big)^t\mathbb E\|x_0-\bar x\|^2+\frac{2\sigma^2\eta}{\hat\alpha}. \tag{7.3}
--   $$
--   2. If $\rho<\frac12$, set $\hat\alpha:=\alpha-2B$. If $\eta\le\dfrac{1}{2(B^2/\hat\alpha+L)}$ and $x_0\in\operatorname{dom}r$, then for every $t\ge0$
--   $$
--   \mathbb E[\varphi(\hat x_t)-\varphi(\bar x)]\le2\Big(1-\frac{\eta\hat\alpha}{2}\Big)^t\big(\varphi(x_0)-\varphi(\bar x)\big)+\sigma^2\eta, \tag{7.4}
--   $$
--   where $\hat x_0=x_0$ and $\hat x_t=(1-\frac{\hat\alpha\eta}2)\hat x_{t-1}+\frac{\hat\alpha\eta}2x_t$.
--
--   Both claims hold with the paper's constants and with no further restriction on $\eta$. When the bias vanishes ($B\to0$) they recover the standard linear convergence of proximal stochastic gradient to an $O(\eta\sigma^2)$ neighbourhood. In the decision-dependent setting of the paper, $B=\gamma\beta$, and Claim 1 is the linear rate of the stochastic gradient method towards the equilibrium point in the regime $\gamma\beta<\alpha$.
--
--   **Formalization Note** Since $x_0$ is a deterministic point, $\mathbb E\|x_0-\bar x\|^2=\|x_0-\bar x\|^2$. Both left sides are expectations of nonnegative quantities, written as Lebesgue integrals in $[0,\infty]$, so no integrability is presupposed. $\varphi(\hat x_t)$ is evaluated at a point of $\operatorname{dom}r$, because $\hat x_t$ is a convex combination of $x_0,\dots,x_t\in\operatorname{dom}r$. No condition $\eta\le1/(2L)$ or $\eta\alpha\le1/2$ is added to Claim 1: the printed proof uses them, but the claim holds without them.
--
--   Differences from the source:
--   - generalization: g_t = g(x_t), a fresh draw with ‖E[g(x)] − ∇f(x)‖ ≤ B‖x − x̄‖ and E‖g(x) − E[g(x)]‖² ≤ σ²; E_t conditions on x_0, …, x_t → the same two bounds conditionally on a filtration 𝓕_t to which x_t is adapted, with g_t 𝓕_{t+1}-measurable and square integrable; reason: a fresh draw satisfies them with 𝓕_t = σ(g_0, …, g_{t−1}), and conditioning on x_0, …, x_t is recovered by the tower property; the proof uses nothing else.
--   - encoding: x_{t+1} = prox_{η r}(x_t − η g_t) = argmin_y {r(y) + ‖y − w‖²/(2η)} → GoldenRatioVI.IsProx D (η · r) w x_{t+1}: x_{t+1} ∈ D minimizes η r(y) + ‖y − w‖²/2; reason: multiplying by η > 0 does not change the minimizers; under Assumption 7 the minimizer exists and is unique.
--   - generalization: Algorithm 1 runs for t = 0, 1, …, T → an infinite run, every t ∈ ℕ; reason: the first T + 1 steps of the infinite run are a run of Algorithm 1 up to T.
--   - encoding: Rd, "a Euclidean space" (p.5) → a finite-dimensional real inner product space E; reason: every such space is isometric to some Rd and the paper calls Rd a Euclidean space.
--   - encoding: r: Rd → R ∪ {∞} closed and convex → the pair (D, r) with GoldenRatioVI.IsProperConvexLsc D r; reason: closed = lower semicontinuous extension; D ≠ ∅ is implicit because φ has a minimizer x̄ ∈ dom r.
--   - encoding: expectations E[·] of nonnegative quantities → lower Lebesgue integrals ∫⁻ ENNReal.ofReal(·) dP in [0, ∞], compared with ENNReal.ofReal of the right side; reason: same value whenever the expectation is finite, and no integrability is presupposed; the right sides are nonnegative under the hypotheses.
--   - encoding: Algorithm 1's input x0, with E‖x0 − x̄‖² on the right of (7.3) → a deterministic point x₀ and ‖x₀ − x̄‖²; reason: the input of Algorithm 1 is a point, as (7.4) and Corollary 7.4 show by using φ(x0) and ‖x0 − x̄‖² with no expectation, so E‖x0 − x̄‖² = ‖x0 − x̄‖².
--   - reading: x̂t defined only recursively, x̂t = (1 − α̂η/2)x̂t−1 + (α̂η/2)xt → x̂0 = x0 (runningAvg); reason: Appendix A (p.47), whose Corollary A.3 the proof applies, fixes x̂0 := x0.
--   - encoding: Claim 2 for any x0 → Claim 2 assumes x₀ ∈ dom r; reason: for x0 ∉ dom r, φ(x0) = +∞ and (7.4) is trivially true; the condition only excludes that case.
-- source:
--   Drusvyatskiy, Xiao, Stochastic optimization with decision-dependent distributions, arXiv:2011.11173v2, Theorem 7.3, p.27

import Mathlib
import Definitions.Def_DecDepSO_Assumption7ab
import Definitions.Def_DecDepSO_IsBiasedProxSGDRun
import Definitions.Def_DecDepSO_runningAvg

open MeasureTheory

namespace DecDepSO

/-- **Theorem 7.3 (Constant step size).**
Drusvyatskiy, Xiao, *Stochastic optimization with decision-dependent distributions*,
arXiv:2011.11173v2, Theorem 7.3, p.27: "Suppose Assumption 7 holds. Let xt be the iterates
generated by Algorithm 1 with a fixed parameter η > 0. Then the following are true.
1. Suppose we are in the regime ρ < 1 and set α̂ := α − B. Then with the parameter
η ≤ 1/(B²/α̂ + L), the estimate holds: E‖xt − x̄‖² ≤ (1 − 2ηα̂/3)^t E‖x0 − x̄‖² + 2σ²η/α̂. (7.3)
2. Suppose we are in the regime ρ < 1/2 and set α̂ := α − 2B. Then with the parameter
η ≤ 1/(2(B²/α̂ + L)), the estimate holds: E[φ(x̂t) − φ(x̄)] ≤ 2(1 − ηα̂/2)^t (φ(x0) − φ(x̄)) + σ²η.
(7.4) where the average iterate is defined recursively by x̂t = (1 − α̂η/2)x̂t−1 + (α̂η/2)xt."

Under Assumption 7 (`Assumption7ab`, and the oracle and run `IsBiasedProxSGDRun` with the
constant step `η > 0` and deterministic start `x₀`), with `φ = f + r` and `ρ = B/α`:
1. if `B/α < 1` and `η ≤ 1/(B²/(α − B) + L)`, then for every `t`,
   `E‖x_t − x̄‖² ≤ (1 − 2η(α − B)/3)^t E‖x_0 − x̄‖² + 2σ²η/(α − B)`;
2. if `B/α < 1/2`, `η ≤ 1/(2(B²/(α − 2B) + L))` and `x₀ ∈ dom r`, then for every `t`,
   `E[φ(x̂_t) − φ(x̄)] ≤ 2(1 − η(α − 2B)/2)^t (φ(x₀) − φ(x̄)) + σ²η`, where `x̂_0 = x_0` and
   `x̂_t = (1 − (α − 2B)η/2) x̂_{t−1} + ((α − 2B)η/2) x_t`.

**Formalization Note.** Both expectations are of nonnegative quantities and are lower Lebesgue
integrals in `[0, ∞]` (`∫⁻` of `ENNReal.ofReal`), compared with `ENNReal.ofReal` of the real right
side; no integrability is presupposed, and a Bochner junk value cannot make the bounds vacuous.
`φ(x̂_t) − φ(x̄) ≥ 0` because `x̂_t ∈ dom r` (a convex combination of points of the convex set
`dom r`) and `x̄` minimizes `φ`. `x̂_0 = x_0` (Appendix A, p.47). Claim 2 assumes `x₀ ∈ dom r`;
otherwise `φ(x₀) = +∞` and (7.4) is trivial. No condition `η ≤ 1/(2L)` or `ηα ≤ 1/2` is added to
Claim 1: the printed proof uses them, but the claim is true without them. -/
theorem theorem_7_3_constant_step {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℕ mΩ}
    {f : E → ℝ} {D : Set E} {r : E → ℝ} {L B α σ : ℝ} {xbar : E}
    {η : ℝ} {x₀ : E} {x g : ℕ → Ω → E}
    (hA : Assumption7ab f D r L B α xbar)
    (hrun : IsBiasedProxSGDRun P 𝓕 f D r B σ xbar (fun _ => η) x₀ x g) :
    (B / α < 1 → η ≤ 1 / (B ^ 2 / (α - B) + L) → ∀ t : ℕ,
      ∫⁻ ω, ENNReal.ofReal (‖x t ω - xbar‖ ^ 2) ∂P ≤
        ENNReal.ofReal ((1 - 2 * η * (α - B) / 3) ^ t * ‖x₀ - xbar‖ ^ 2
          + 2 * σ ^ 2 * η / (α - B))) ∧
    (B / α < 1 / 2 → η ≤ 1 / (2 * (B ^ 2 / (α - 2 * B) + L)) → x₀ ∈ D → ∀ t : ℕ,
      ∫⁻ ω, ENNReal.ofReal
          ((f (runningAvg (fun _ => (α - 2 * B) * η / 2) x t ω)
              + r (runningAvg (fun _ => (α - 2 * B) * η / 2) x t ω))
            - (f xbar + r xbar)) ∂P ≤
        ENNReal.ofReal (2 * (1 - η * (α - 2 * B) / 2) ^ t * ((f x₀ + r x₀) - (f xbar + r xbar))
          + σ ^ 2 * η)) := by sorry

end DecDepSO
