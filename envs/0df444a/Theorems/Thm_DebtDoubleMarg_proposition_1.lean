-- Prove2me | Theorems.Thm_DebtDoubleMarg_proposition_1
-- name    : DebtDoubleMarg.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:59.154402+00:00
-- url     : https://prove2.me/theorems/74453001-2891-4392-ad72-4aac35de6387
-- title:
--   Proposition 1 — the lender's optimal scheme is (6); the firm invests at $X_F^*$ with $I^{opt}=\frac1{2\eta(\beta_1+1)}$ at coupon $\rho^{opt}=\frac{r\beta_1}{\beta_1-1}>r$
-- statement:
--   Consider the lender–firm investment model of this mission in the scenario without a bankruptcy option: the demand level is a geometric Brownian motion with drift $\mu$ and volatility $\sigma$, driven by a standard Brownian motion; the parameters satisfy $\eta>0$, $r>\mu$, $\delta>0$, $\sigma>0$, $r>0$. Let $\beta_1$ be given by the quadratic formula, $d=\delta(r-\mu)$, and
--   $$X^*_F=\frac{\beta_1+1}{\beta_1-1}\,d,\qquad \rho^{NBO}(X)=\begin{cases}\dfrac{r(X+d)}{2d} & X\ge X^*_F,\\ \infty & \text{otherwise}.\end{cases}\tag{6}$$
--   Then:
--
--   1. $\beta_1$ is a root of $\tfrac12\sigma^2\beta^2+(\mu-\tfrac12\sigma^2)\beta-r=0$, every root is at most $\beta_1$, and $\beta_1>1$.
--   2. **The lender's optimal strategy is (6).** For every initial demand level $x_0>0$, the threshold $X^*_F$ is optimal for the firm under $\rho^{NBO}$, and for every coupon scheme $\rho$ and every threshold $X_F$ that is optimal for the firm at $x_0$ under $\rho$,
--   $$V_D(x_0;\rho,X_F)\le V_D(x_0;\rho^{NBO},X^*_F).$$
--   3. **Waiting region.** If $0<x_0<X^*_F$, then $X^*_F$ is the only optimal threshold of the firm under $\rho^{NBO}$: the firm waits until demand reaches $X^*_F$.
--   4. **Stopping region.** If $x_0\ge X^*_F$, every optimal threshold of the firm under $\rho^{NBO}$ is at most $x_0$: the firm invests immediately.
--   5. **Investment size.** For every $X\ge X^*_F$, $\rho^{NBO}(X)$ is finite and the firm's unique optimal capacity is
--   $$I^{NBO}\big(X,\rho^{NBO}(X)\big)=\frac1{4\eta}\Big(1-\frac{\delta(r-\mu)}{X}\Big).$$
--   6. **At the trigger.** $X^*_F>0$, the coupon rate is $\rho^{opt}=\rho^{NBO}(X^*_F)=r\dfrac{\beta_1}{\beta_1-1}>r$, and the capacity is $I^{opt}=I^{NBO}(X^*_F,\rho^{opt})=\dfrac1{2\eta(\beta_1+1)}$.
--
--   Compared with internal financing (Huisman and Kort 2015), the investment timing is the same and the capacity is halved: the lender's markup over the risk-free rate is a double marginalization of financing.
--
--   **Formalization Note** The payoffs $V_F$, $V_D$, $J_F$, $J_D$ and the optimal capacity are defined by the paper's expectations and optimization problems; only $\beta_1$, $X^*_F$ and the scheme (6) are transcribed. The firm's strategies are thresholds, and an infinite coupon gives both players zero.
--
--   Differences from the source:
--   - reading: "the lender's optimal strategy is given by (6)" (problem (4): sup over ρ(·) of V_D(X, ρ(·)) with the firm's solution X∗_F(ρ(·)) of (2)) → for every x₀ > 0: X*_F is firm-optimal under ρ^NBO, and for every scheme ρ with values in [0, ∞] and every threshold X_F firm-optimal at x₀ under ρ, V_D(x₀; ρ, X_F) ≤ V_D(x₀; ρ^NBO, X*_F); reason: (4) read for every initial level (Markov perfection, §2.2) and against every optimal response of the firm, the stronger reading when the firm's optimum is not unique; uniqueness of the optimal scheme is not claimed (endnote 8)
--   - reading: "for X < X∗_F, the firm waits until the demand level reaches X∗_F … For X ≥ X∗_F, the firm invests immediately" → for 0 < x₀ < X*_F, X*_F is the only firm-optimal threshold under ρ^NBO; for x₀ ≥ X*_F every firm-optimal threshold is ≤ x₀; reason: p.6 announces "a unique investment threshold"; for x₀ ≥ X*_F every threshold ≤ x₀ means the same immediate investment, so uniqueness is not claimed there
--   - encoding: the firm's stopping region [X_F, ∞) (p.6, endnote 6) → the firm chooses a threshold X_F ≥ 0; it waits if x₀ < X_F and invests at once otherwise; reason: the paper's own restriction to threshold strategies
--   - encoding: ρ(X) = ∞ (financing refused) → WithTop ℝ with ⊤, and J_F(X, ⊤) = J_D(X, ⊤) = 0; reason: at an infinite coupon nothing is invested and no cash flows occur
--   - encoding: J_D(X, ρ) = E₀{∫₀^∞ ρδI* e^{−rt}dt − δI*} ((3) with τ_B = ∞) → the same expression without E₀; reason: the integrand is deterministic once X and ρ are fixed, so the expectation under a probability measure is the expression itself
--   - encoding: no bankruptcy option (§3.1): the firm pays coupons perpetually → bankruptcy time τ_B = ∞: integrals over (0, ∞), no bankruptcy term, no α; reason: this is the scenario of Proposition 1
--   - encoding: dx(t) = µx(t)dt + σx(t)dω(t), x(0) = X (p.4) → x(t) = X·exp((µ − σ²/2)t + σW_t) for a Mathlib Brownian motion W (IsBrownianReal), on any probability space; reason: the unique strong solution of the SDE; the statement holds for every probability space carrying a Brownian motion
--   - encoding: σ and r not restricted beyond r > µ, δ called "the unit investment cost" (p.4) → hypotheses σ > 0, r > 0 and δ > 0 (in Params.Standing); reason: r > 0 makes ∫₀^∞ e^{−rt}dt finite and σ ≠ 0 makes the quadratic defining β₁ have two roots; σ > 0 is the volatility convention; δ > 0 is the positivity of a cost and (6) divides by δ(r − µ); only undefined or degenerate cases are excluded
-- source:
--   Huberts, Wen, Dawid, Huisman, Kort, Double Marginalization Because of External Financing: Capacity Investment Under Uncertainty, Management Science (2025), doi:10.1287/mnsc.2023.01152, Proposition 1 and (6), p.7

import Mathlib
import Definitions.Def_DebtDoubleMarg_GeometricBM
import Definitions.Def_DebtDoubleMarg_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DebtDoubleMarg

/-- **Proposition 1 (no bankruptcy option).** Under the standing assumptions (`η > 0`, `r > µ`,
`δ > 0`, `σ > 0`, `r > 0`), for any standard Brownian motion `W` driving the demand level,
write `β₁` for `beta1 µ σ r`, `d = δ(r − µ)` and `X*_F = (β₁ + 1)/(β₁ − 1) · d`. Then:
1. `β₁` is a root of `½σ²β² + (µ − ½σ²)β − r = 0`, every root is `≤ β₁`, and `β₁ > 1`;
2. for every initial level `x₀ > 0`: `X*_F` is a firm-optimal threshold under `ρ^NBO`, and for
   every coupon scheme `ρ` and every threshold `X_F` firm-optimal at `x₀` under `ρ`,
   `V_D(x₀; ρ, X_F) ≤ V_D(x₀; ρ^NBO, X*_F)` (the lender's optimal strategy is (6));
3. for `0 < x₀ < X*_F`, `X*_F` is the only firm-optimal threshold under `ρ^NBO` (the firm waits
   until demand reaches `X*_F`);
4. for `x₀ ≥ X*_F`, every firm-optimal threshold under `ρ^NBO` is `≤ x₀` (immediate investment);
5. for `X ≥ X*_F`, `ρ^NBO(X)` is finite and `I^NBO(X, ρ^NBO(X)) = (1/(4η))(1 − d/X)` is the unique
   maximizer of `J̃_F(X, ρ^NBO(X), ·)` on `I ≥ 0`;
6. `X*_F > 0`, `ρ^opt = ρ^NBO(X*_F) = rβ₁/(β₁ − 1) > r` and `I^opt = I^NBO(X*_F, ρ^opt) = 1/(2η(β₁ + 1))`.

Huberts, Wen, Dawid, Huisman, Kort, *Double Marginalization Because of External Financing:
Capacity Investment Under Uncertainty*, Management Science (2025), doi:10.1287/mnsc.2023.01152,
Proposition 1 and (6), p.7.

**Formalization Note** The firm uses threshold strategies (p.6, endnote 6); `ρ = ∞` is `⊤` with
zero payoffs; optimality of (6) is not claimed unique (endnote 8). -/
theorem proposition_1 (p : Params) (hp : p.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) :
    -- (1) β₁ is the larger root of the fundamental quadratic and exceeds 1
    (p.σ ^ 2 / 2 * beta1 p.μ p.σ p.r ^ 2 + (p.μ - p.σ ^ 2 / 2) * beta1 p.μ p.σ p.r - p.r = 0 ∧
      (∀ β : ℝ, p.σ ^ 2 / 2 * β ^ 2 + (p.μ - p.σ ^ 2 / 2) * β - p.r = 0 → β ≤ beta1 p.μ p.σ p.r) ∧
      1 < beta1 p.μ p.σ p.r) ∧
    -- (2) the lender's optimal strategy is (6), from every initial level
    (∀ x0 : ℝ, 0 < x0 →
      IsFirmOptimal p P W (nboScheme p) x0 (nboTrigger p) ∧
      ∀ ρ : ℝ → WithTop ℝ, IsCouponScheme ρ → ∀ XF : ℝ, IsFirmOptimal p P W ρ x0 XF →
        lenderPayoff p P W ρ x0 XF ≤ lenderPayoff p P W (nboScheme p) x0 (nboTrigger p)) ∧
    -- (3) below the trigger the firm waits for X*_F, and X*_F is its only optimal threshold
    (∀ x0 : ℝ, 0 < x0 → x0 < nboTrigger p → ∀ XF : ℝ,
      IsFirmOptimal p P W (nboScheme p) x0 XF → XF = nboTrigger p) ∧
    -- (4) at or above the trigger the firm invests immediately
    (∀ x0 : ℝ, nboTrigger p ≤ x0 → ∀ XF : ℝ,
      IsFirmOptimal p P W (nboScheme p) x0 XF → XF ≤ x0) ∧
    -- (5) the investment size for X ≥ X*_F
    (∀ X : ℝ, nboTrigger p ≤ X → ∃ ρ : ℝ, nboScheme p X = (ρ : WithTop ℝ) ∧
      (∀ I : ℝ, IsOptimalSize p P W X ρ I ↔
        I = 1 / (4 * p.η) * (1 - p.δ * (p.r - p.μ) / X)) ∧
      optSize p P W X ρ = 1 / (4 * p.η) * (1 - p.δ * (p.r - p.μ) / X)) ∧
    -- (6) the trigger, the coupon rate and the size at the trigger
    (0 < nboTrigger p ∧
      nboTrigger p = (beta1 p.μ p.σ p.r + 1) / (beta1 p.μ p.σ p.r - 1) * (p.δ * (p.r - p.μ)) ∧
      ∃ ρopt : ℝ, nboScheme p (nboTrigger p) = (ρopt : WithTop ℝ) ∧
        ρopt = p.r * (beta1 p.μ p.σ p.r / (beta1 p.μ p.σ p.r - 1)) ∧ p.r < ρopt ∧
        optSize p P W (nboTrigger p) ρopt = 1 / (2 * p.η * (beta1 p.μ p.σ p.r + 1))) := by sorry

end DebtDoubleMarg
