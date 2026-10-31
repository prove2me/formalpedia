-- Prove2me | Theorems.Thm_DecDepSO_lemma_A_2
-- name    : DecDepSO.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:43.125647+00:00
-- url     : https://prove2.me/theorems/2b754f7e-b13c-498f-951b-3c10b15f9f1c
-- title:
--   Lemma A.2 (Averaging) — (A.1) implies $\frac{\mathbb E[h(\hat x_t)]}{c_1+c_2}+D_t\le\hat\Gamma_t\big(\frac{h(x_0)}{c_1+c_2}+D_0+\sum_{i=1}^t\frac{\omega_i}{\hat\Gamma_i(1+c_2\delta_i)}\big)$
-- statement:
--   Let $h$ be a convex function with domain $\operatorname{dom}h$ and let $(x_t)_{t\ge0}$ be random vectors in $\operatorname{dom}h$ with $\mathbb E|h(x_t)|<\infty$. Let $c_1,c_2\in\mathbb R$ and let $(\delta_t)_{t\ge1}$, $(D_t)_{t\ge0}$, $(\omega_t)_{t\ge1}$ be nonnegative sequences satisfying
--   $$
--   \delta_t\,\mathbb E[h(x_t)]\le(1-c_1\delta_t)D_{t-1}-(1+c_2\delta_t)D_t+\omega_t\qquad\forall t\ge1, \tag{A.1}
--   $$
--   and suppose $c_1+c_2>0$, $1-c_1\delta_t>0$ and $1+c_2\delta_t>0$ for all $t\ge1$. Define the augmented weights, their partial products and the running average
--   $$
--   \hat\delta_t:=\frac{\delta_t(c_1+c_2)}{1+c_2\delta_t},\qquad \hat\Gamma_t:=\prod_{i=1}^t(1-\hat\delta_i),\qquad \hat x_0:=x_0,\quad \hat x_t:=(1-\hat\delta_t)\hat x_{t-1}+\hat\delta_t x_t .
--   $$
--   Then for every $t\ge0$,
--   $$
--   \frac{\mathbb E[h(\hat x_t)]}{c_1+c_2}+D_t\ \le\ \hat\Gamma_t\Big(\frac{\mathbb E[h(x_0)]}{c_1+c_2}+D_0+\sum_{i=1}^t\frac{\omega_i}{\hat\Gamma_i(1+c_2\delta_i)}\Big). \tag{A.2}
--   $$
--
--   This converts a one-step recursion for a stochastic algorithm into a bound on the function value at the averaged iterate; Corollary A.3 is its constant-parameter case and gives Claim 2 of Theorem 7.3.
--
--   **Formalization Note** The extended-valued $h$ is a set $\operatorname{dom}$ and real values on it, convex on $\operatorname{dom}$. $\mathbb E[h(\hat x_t)]$ is the published extended expectation `WassersteinDRO.Duality.erealExpectation` (it can be $-\infty$, and is $+\infty$ whenever $\mathbb E[h(\hat x_t)^+]=\infty$, so the inequality also proves $\mathbb E[h(\hat x_t)^+]<\infty$); $h(\hat x_t)$ is assumed to be a random variable. Division by $c_1+c_2>0$ is multiplication by its inverse. The values $\delta_0$, $\omega_0$ are not used.
--
--   Differences from the source:
--   - reading: "h(x)" on the right side, with no x quantified → E[h(x0)], the expectation at the initial point x̂0 = x0; reason: x̂t is a convex combination of x0, …, xt with weight Γ̂t on x0, and Theorem 7.3 applies the bound with φ(x0) − φ(x̄); for a deterministic x0 this is h(x0).
--   - encoding: a convex function h: Rd → R ∪ {∞} and random vectors xt in dom h → a set dom and h: E → R with ConvexOn ℝ dom h, and xt(ω) ∈ dom for every ω; reason: an extended-valued function is convex exactly when its domain is convex and it is convex there; values off dom are irrelevant.
--   - encoding: E[h(xt)] in (A.1), presupposed to exist → h(xt) integrable for every t ≥ 0; reason: the expectations in (A.1) and E[h(x0)] are real numbers on the page.
--   - encoding: E[h(x̂t)], presupposed to exist → WassersteinDRO.Duality.erealExpectation of h(x̂t): E[h⁺] − E[h⁻] in [−∞, ∞), and +∞ whenever E[h⁺] = ∞, with h(x̂t) assumed a.e. strongly measurable; reason: h(x̂t) is bounded above by an integrable function but need not be integrable from below, so its expectation may be −∞; measurability is what the page presupposes when it writes E[h(x̂t)]; the +∞ convention applies only where the page's expectation is undefined or +∞, and the conclusion rules that case out.
--   - generalization: the inequality, with E[h(x̂t)] presupposed to be defined → the same inequality in [−∞, ∞], which also forces E[h(x̂t)⁺] < ∞ (the left side would otherwise be +∞); reason: a stronger conclusion: it proves that the page's expectation is defined and not +∞.
--   - generalization: Rd → any real inner product space E; reason: the statement specializes to Rd; no finite dimensionality is used.
-- source:
--   Drusvyatskiy, Xiao, Stochastic optimization with decision-dependent distributions, arXiv:2011.11173v2, Lemma A.2, p.47, with (A.1), p.46, and the definitions of δ̂t, Γ̂t, x̂t, p.47

import Mathlib
import Definitions.Def_DecDepSO_runningAvg
import Definitions.Def_WassersteinDRO_Duality_erealExpectation

open MeasureTheory

namespace DecDepSO

/-- **Lemma A.2 (Averaging).**
Drusvyatskiy, Xiao, *Stochastic optimization with decision-dependent distributions*,
arXiv:2011.11173v2, Lemma A.2, p.47, with (A.1) on p.46 and the definitions of δ̂t, Γ̂t, x̂t on
p.47: "Consider a convex function h: Rd → R∪{∞} and let {xt}t≥0 ⊂ Rd be a sequence of random
vectors in dom h. Suppose that there are constants c1, c2 ∈ R and nonnegative sequences {δt}t≥1,
{Dt}t≥0, and {ωt}t≥1 satisfying (A.1). Suppose moreover the relations c1 + c2 > 0, 1 − c1δt > 0,
and 1 + c2δt > 0 hold for all t ≥ 1. Then the estimate holds:
E[h(x̂t)]/(c1 + c2) + Dt ≤ Γ̂t ( h(x)/(c1 + c2) + D0 + ∑_{i=1}^t ωi/(Γ̂i(1 + c2δi)) ). (A.2)"
Here (A.1) is `δt · E[h(xt)] ≤ (1 − c1δt)Dt−1 − (1 + c2δt)Dt + ωt ∀t ≥ 1`,
`δ̂t := δt(c1 + c2)/(1 + c2δt)`, `Γ̂t := ∏_{i=1}^t (1 − δ̂i)`, `x̂0 := x0`,
`x̂t := (1 − δ̂t)x̂t−1 + δ̂txt`.

Let `h` be convex on the convex set `dom` and finite there, `x_t` random points of `dom`
with `h(x_t)` integrable, and let `c₁, c₂, δ, D, ω` satisfy the hypotheses above. Then for every
`t`,
`E[h(x̂_t)]/(c₁ + c₂) + D_t ≤ Γ̂_t (E[h(x_0)]/(c₁ + c₂) + D_0 + ∑_{i=1}^t ω_i/(Γ̂_i(1 + c₂δ_i)))`,
with `E[h(x̂_t)]` the extended expectation.

**Formalization Note.** The extended-valued `h` is the pair `(dom, h)`; "convex" is
`ConvexOn ℝ dom h` (which includes convexity of `dom`). The page's "h(x)" is read as
`E[h(x_0)]`, the value at the initial point `x̂_0 = x_0` (`= h(x_0)` for a deterministic `x_0`).
The expectations `E[h(x_t)]` in (A.1) presuppose that `h(x_t)` is integrable, and `E[h(x̂_t)]`
that `h(x̂_t)` is a random variable (a.e. strongly measurable); both are assumed. `E[h(x̂_t)]` is
the published extended expectation `WassersteinDRO.Duality.erealExpectation`
(`E[h⁺] − E[h⁻] ∈ [−∞, ∞)`, and `+∞` whenever `E[h⁺] = ∞`): `h(x̂_t)` need not be integrable from
below, so the value can be `−∞`. Since the right side is a real number, the inequality also
asserts `E[h(x̂_t)⁺] < ∞`. Division by `c₁ + c₂ > 0` is multiplication by `(c₁ + c₂)⁻¹`. The values
`δ_0`, `ω_0` are unused. -/
theorem lemma_A_2 {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {dom : Set E} {h : E → ℝ} (hh : ConvexOn ℝ dom h)
    {x : ℕ → Ω → E} (hx : ∀ t ω, x t ω ∈ dom)
    (hint : ∀ t, Integrable (fun ω => h (x t ω)) P)
    (c₁ c₂ : ℝ) (δ D ω : ℕ → ℝ)
    (hδ : ∀ t, 1 ≤ t → 0 ≤ δ t) (hD : ∀ t, 0 ≤ D t) (hω : ∀ t, 1 ≤ t → 0 ≤ ω t)
    (hA1 : ∀ t, 1 ≤ t →
      δ t * ∫ ω', h (x t ω') ∂P ≤ (1 - c₁ * δ t) * D (t - 1) - (1 + c₂ * δ t) * D t + ω t)
    (hc : 0 < c₁ + c₂) (hc₁ : ∀ t, 1 ≤ t → 0 < 1 - c₁ * δ t)
    (hc₂ : ∀ t, 1 ≤ t → 0 < 1 + c₂ * δ t)
    (hmeas : ∀ t, AEStronglyMeasurable
      (fun ω' => h (runningAvg (fun i => δ i * (c₁ + c₂) / (1 + c₂ * δ i)) x t ω')) P)
    (t : ℕ) :
    (((c₁ + c₂)⁻¹ : ℝ) : EReal) *
        WassersteinDRO.Duality.erealExpectation P
          (fun ω' => ((h (runningAvg (fun i => δ i * (c₁ + c₂) / (1 + c₂ * δ i)) x t ω') : ℝ)
            : EReal))
      + ((D t : ℝ) : EReal) ≤
      (((∏ i ∈ Finset.Icc 1 t, (1 - δ i * (c₁ + c₂) / (1 + c₂ * δ i))) *
        ((∫ ω', h (x 0 ω') ∂P) / (c₁ + c₂) + D 0 +
          ∑ i ∈ Finset.Icc 1 t, ω i /
            ((∏ j ∈ Finset.Icc 1 i, (1 - δ j * (c₁ + c₂) / (1 + c₂ * δ j))) *
              (1 + c₂ * δ i))) : ℝ) : EReal) := by sorry

end DecDepSO
