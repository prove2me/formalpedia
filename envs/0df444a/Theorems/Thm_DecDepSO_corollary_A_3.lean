-- Prove2me | Theorems.Thm_DecDepSO_corollary_A_3
-- name    : DecDepSO.corollary_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:32.464101+00:00
-- url     : https://prove2.me/theorems/87a5f194-a80d-4e57-8988-0b6311b58717
-- title:
--   Corollary A.3 (Constant parameter) — $\mathbb E[h(\hat x_t)]+(c_1+c_2)D_t\le\big(\frac{1-c_1\delta}{1+c_2\delta}\big)^t(h(x_0)+(c_1+c_2)D_0)+\frac\omega\delta$
-- statement:
--   Assume the setting of Lemma A.2 with constant parameters $\delta_t=\delta>0$ and $\omega_t=\omega\ge0$: $h$ is convex with domain $\operatorname{dom}h$, the random vectors $x_t\in\operatorname{dom}h$ have $\mathbb E|h(x_t)|<\infty$, $D_t\ge0$,
--   $$
--   \delta\,\mathbb E[h(x_t)]\le(1-c_1\delta)D_{t-1}-(1+c_2\delta)D_t+\omega\qquad\forall t\ge1,
--   $$
--   and $c_1+c_2>0$, $1-c_1\delta>0$, $1+c_2\delta>0$. Let $\hat x_t$ be the running average with the constant weight $\hat\delta=\delta(c_1+c_2)/(1+c_2\delta)$. Then for every $t\ge0$,
--   $$
--   \mathbb E[h(\hat x_t)]+(c_1+c_2)D_t\ \le\ \Big(\frac{1-c_1\delta}{1+c_2\delta}\Big)^t\big(\mathbb E[h(x_0)]+(c_1+c_2)D_0\big)+\frac\omega\delta. \tag{A.3}
--   $$
--
--   With $h=\varphi-\varphi(\bar x)$, $D_t=\mathbb E\|x_t-\bar x\|^2$, $\delta=2\eta$, $c_1=\hat\alpha/4$, $c_2=0$ and $\omega=2\eta^2\sigma^2$ this gives the estimate (7.4) of Theorem 7.3.
--
--   **Formalization Note** $\mathbb E[h(\hat x_t)]$ is the published extended expectation `WassersteinDRO.Duality.erealExpectation`, as in Lemma A.2, and $h(\hat x_t)$ is assumed to be a random variable.
--
--   Differences from the source:
--   - reading: "h(x)" on the right side, with no x quantified → E[h(x0)], the expectation at the initial point x̂0 = x0; reason: x̂t is a convex combination of x0, …, xt with weight Γ̂t on x0, and Theorem 7.3 applies the bound with φ(x0) − φ(x̄); for a deterministic x0 this is h(x0).
--   - encoding: a convex function h: Rd → R ∪ {∞} and random vectors xt in dom h → a set dom and h: E → R with ConvexOn ℝ dom h, and xt(ω) ∈ dom for every ω; reason: an extended-valued function is convex exactly when its domain is convex and it is convex there; values off dom are irrelevant.
--   - encoding: E[h(xt)] in (A.1), presupposed to exist → h(xt) integrable for every t ≥ 0; reason: the expectations in (A.1) and E[h(x0)] are real numbers on the page.
--   - encoding: E[h(x̂t)], presupposed to exist → WassersteinDRO.Duality.erealExpectation of h(x̂t): E[h⁺] − E[h⁻] in [−∞, ∞), and +∞ whenever E[h⁺] = ∞, with h(x̂t) assumed a.e. strongly measurable; reason: h(x̂t) is bounded above by an integrable function but need not be integrable from below, so its expectation may be −∞; measurability is what the page presupposes when it writes E[h(x̂t)]; the +∞ convention applies only where the page's expectation is undefined or +∞, and the conclusion rules that case out.
--   - generalization: the inequality, with E[h(x̂t)] presupposed to be defined → the same inequality in [−∞, ∞], which also forces E[h(x̂t)⁺] < ∞ (the left side would otherwise be +∞); reason: a stronger conclusion: it proves that the page's expectation is defined and not +∞.
--   - generalization: Rd → any real inner product space E; reason: the statement specializes to Rd; no finite dimensionality is used.
--   - encoding: δt = δ ≥ 0 (nonnegative, as in Lemma A.2) → δ > 0; reason: the right side contains ω/δ, undefined at δ = 0; the condition only excludes that undefined case.
-- source:
--   Drusvyatskiy, Xiao, Stochastic optimization with decision-dependent distributions, arXiv:2011.11173v2, Corollary A.3, p.48

import Mathlib
import Definitions.Def_DecDepSO_runningAvg
import Definitions.Def_WassersteinDRO_Duality_erealExpectation

open MeasureTheory

namespace DecDepSO

/-- **Corollary A.3 (Constant parameter).**
Drusvyatskiy, Xiao, *Stochastic optimization with decision-dependent distributions*,
arXiv:2011.11173v2, Corollary A.3, p.48: "Assume the setting of Lemma A.2, and suppose that
δt = δ and ωi = ω are constant. Then the estimate holds:
E[h(x̂t)] + (c1 + c2)Dt ≤ ((1 − c1δ)/(1 + c2δ))^t (h(x) + (c1 + c2)D0) + ω/δ. (A.3)"

In the setting of Lemma A.2 (`h` convex on `dom`, `x_t ∈ dom` with `h(x_t)` integrable, (A.1)
for all `t ≥ 1`, `c₁ + c₂ > 0`, `1 − c₁δ > 0`, `1 + c₂δ > 0`, `D_t ≥ 0`, `ω ≥ 0`) with constant
`δ > 0` and `ω`, and with `x̂` the running average with weight `δ̂ = δ(c₁ + c₂)/(1 + c₂δ)`, for
every `t`,
`E[h(x̂_t)] + (c₁ + c₂)D_t ≤ ((1 − c₁δ)/(1 + c₂δ))^t (E[h(x_0)] + (c₁ + c₂)D_0) + ω/δ`.

**Formalization Note.** `δ > 0` (instead of the nonnegativity of Lemma A.2) because the right side
contains `ω/δ`, undefined at `δ = 0`. "h(x)" is read as `E[h(x_0)]`, as in Lemma A.2. `E[h(x̂_t)]`
is the published extended expectation `WassersteinDRO.Duality.erealExpectation` (possibly `−∞`;
`+∞` whenever `E[h⁺] = ∞`, so the inequality also asserts `E[h(x̂_t)⁺] < ∞`); measurability of
`h(x̂_t)` is assumed, as the page presupposes it. -/
theorem corollary_A_3 {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {dom : Set E} {h : E → ℝ} (hh : ConvexOn ℝ dom h)
    {x : ℕ → Ω → E} (hx : ∀ t ω, x t ω ∈ dom)
    (hint : ∀ t, Integrable (fun ω => h (x t ω)) P)
    (c₁ c₂ δ ω : ℝ) (D : ℕ → ℝ)
    (hδ : 0 < δ) (hD : ∀ t, 0 ≤ D t) (hω : 0 ≤ ω)
    (hA1 : ∀ t, 1 ≤ t →
      δ * ∫ ω', h (x t ω') ∂P ≤ (1 - c₁ * δ) * D (t - 1) - (1 + c₂ * δ) * D t + ω)
    (hc : 0 < c₁ + c₂) (hc₁ : 0 < 1 - c₁ * δ) (hc₂ : 0 < 1 + c₂ * δ)
    (hmeas : ∀ t, AEStronglyMeasurable
      (fun ω' => h (runningAvg (fun _ => δ * (c₁ + c₂) / (1 + c₂ * δ)) x t ω')) P)
    (t : ℕ) :
    WassersteinDRO.Duality.erealExpectation P
        (fun ω' => ((h (runningAvg (fun _ => δ * (c₁ + c₂) / (1 + c₂ * δ)) x t ω') : ℝ) : EReal))
      + (((c₁ + c₂) * D t : ℝ) : EReal) ≤
      ((((1 - c₁ * δ) / (1 + c₂ * δ)) ^ t * ((∫ ω', h (x 0 ω') ∂P) + (c₁ + c₂) * D 0)
        + ω / δ : ℝ) : EReal) := by sorry

end DecDepSO
