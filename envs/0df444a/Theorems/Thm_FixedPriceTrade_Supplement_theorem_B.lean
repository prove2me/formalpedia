-- Prove2me | Theorems.Thm_FixedPriceTrade_Supplement_theorem_B
-- name    : FixedPriceTrade.Supplement.theorem_B
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:16:52.327642+00:00
-- url     : https://prove2.me/theorems/10467fdc-8fe7-4c04-bfe3-8ab06384ea92
-- title:
--   Theorem B — the complete gains-from-trade frontier: $\delta(1/S(C))=\tau(C)/S(C)$ and $\rho(\kappa(C))=1/(1+C\mathcal I(C))$
-- statement:
--   Consider the single-unit model with independent nonnegative values, $0<\mathbb E\max\{V_s,V_b\}<\infty$, the sharp affine coefficient $\delta(\beta)$ and the conditional guarantee $\rho(\kappa)$ of (9)–(10). For $\tfrac14<C<\tfrac12$ let $\beta(C)=1/S(C)$, $u=1-2C$ and $\kappa(C)=\tau(C)(S(C)+u)/u$. Then:
--
--   1. **The frontier (11).** For every $C\in(\tfrac14,\tfrac12)$, every admissible pair satisfies
--   $$
--   \Gamma_{\max}\ \ge\ \frac{1}{S(C)}\,G-\frac{\tau(C)}{S(C)}\,M,
--   $$
--   for every $\delta'<\tau(C)/S(C)$ some bounded admissible pair has $\Gamma_{\max}<\beta(C)G-\delta'M$, and hence $\delta(\beta(C))=\tau(C)/S(C)$.
--   2. **Entire frontier.** $C\mapsto\beta(C)$ maps $(\tfrac14,\tfrac12)$ onto $(0,1)$.
--   3. **Refutation.** For every $\beta\in(0,1)$, every coefficient $\delta'<\delta(\beta)$ is refuted by a bounded admissible pair: $\Gamma_{\max}<\beta G-\delta'M$.
--   4. **Shape.** $\delta$ is strictly increasing, strictly convex and differentiable on $(0,1)$; $\delta'(\beta)\to0$ as $\beta\downarrow0$, $\delta'(\beta)\to\infty$ as $\beta\uparrow1$, and $\delta'$ takes every value in $(0,\infty)$.
--   5. **(12).** $\kappa$ is a strictly increasing bijection from $(\tfrac14,\tfrac12)$ onto $(0,\infty)$.
--   6. **(13).** For every $C\in(\tfrac14,\tfrac12)$,
--   $$
--   \rho(\kappa(C))=\frac1{S(C)+u}=\frac1{1+C\,\mathcal I(C)};
--   $$
--   every admissible pair with $M>0$ and $G/M=\kappa(C)$ has $\Gamma_{\max}/G\ge1/(S(C)+u)$, and for every $\varepsilon>0$ some bounded admissible pair with exactly $G/M=\kappa(C)$ has $\Gamma_{\max}/G<1/(S(C)+u)+\varepsilon$.
--   7. **(14).** For every $\kappa>0$,
--   $$
--   \kappa\,\rho(\kappa)=\delta^*(\kappa)=\sup_{0<\beta<1}\{\kappa\beta-\delta(\beta)\}.
--   $$
--
--   The theorem gives every sharp affine trade-off between the gains from trade and the seller's welfare that a fixed price can guarantee, and the exact gains-from-trade guarantee once $G/M$ is known; the welfare constant of Theorem A is the point of this frontier on the line $\delta=1-\beta$.
--
--   **Formalization Note** Pairs are the published `IsAdmissiblePair` laws and $M$, $G$, $\Gamma_{\max}$, $S$, $\tau$, $\mathcal I$ the published definitions. Because $\delta$ and $\rho$ are infima, the bounds and their sharpness are stated together with the values. The supremum in (14) is stated as a least upper bound.
--
--   Differences from the source:
--   - encoding: "every pair in Section 3" → every pair satisfying the published IsAdmissiblePair; reason: the published definition is exactly the model of Section 3
--   - encoding: M > 0, G/M = κ → 0 < M and G = κ·M; reason: the same condition without a division
--   - encoding: δ(β(C)) = τ(C)/S(C) and ρ(κ(C)) = 1/(S(C)+u), with δ, ρ infima → the value equations together with the lower bound on every admissible pair and the approximating/refuting bounded pairs; reason: a value equation for sInf alone could be met by a default value; the added clauses say the same thing
--   - reading: "The scalar curve (4) gives the entire frontier" → C ↦ 1/S(C) maps (1/4, 1/2) onto (0, 1), plus (11) for every C; reason: "entire" means every β ∈ (0,1) is some β(C)
--   - reading: "Every coefficient smaller than δ(β) is refuted by a bounded hard pair of independent distributions" → for every β ∈ (0,1) and δ′ < δ(β) there is an admissible pair (product law) with both laws carried by some [0, R] and Γmax < βG − δ′M; reason: "hard" names the witnessing pair; bounded and independent are stated
--   - reading: "Its derivative ranges from zero to infinity" → δ differentiable on (0,1), deriv δ → 0 at 0⁺, deriv δ → +∞ at 1⁻, and deriv δ maps (0,1) onto (0, ∞); reason: the literal content of the sentence; both limits are kept
--   - encoding: κρ(κ) = δ*(κ) := sup_{0<β<1}{κβ − δ(β)}, δ extended by +∞ outside (0,1) → IsLUB of {κβ − δ(β) : 0 < β < 1} at κ·ρ(κ), for every κ > 0; reason: the +∞ extension only restricts the supremum to (0,1); IsLUB avoids the default value of sSup
--   - encoding: "For each fixed κ, bounded hard pairs with exactly G/M = κ approach (13)" → for every C ∈ (1/4,1/2) and ε > 0, a bounded admissible pair with G = κ(C)M has Γmax/G < 1/(S(C)+u) + ε; reason: κ is onto (0,∞) (clause 5), so quantifying over C covers every fixed κ > 0; with the lower bound this is convergence to ρ(κ)
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 2683234615efe3b875b8a3f0cde6b0637c6b82cf550767823ebc24d5cd1bca0e), Theorem B, p.12 (PDF p.12); definitions (9)–(10), p.11

import Mathlib
import Definitions.Def_FixedPriceTrade_welfareRatio
import Definitions.Def_FixedPriceTrade_SCurve
import Definitions.Def_FixedPriceTrade_Supplement_deltaSharp

set_option autoImplicit false

namespace FixedPriceTrade.Supplement

open MeasureTheory Set Filter Topology

/-- **Theorem B (sharp affine and conditional GFT guarantees)** — Lin, Shi, Dong, Li, Yu, Zhang,
*The Exact Welfare Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256
26832346…), p.12 (definitions (9)–(10), p.11).

1. (11) For `1/4 < C < 1/2`: every admissible pair has `Γ_max ≥ β(C) G − (τ(C)/S(C)) M`; every
   smaller coefficient is refuted by a bounded admissible pair; hence `δ(β(C)) = τ(C)/S(C)`.
2. The entire frontier: `β(C) = 1/S(C)` maps `(1/4, 1/2)` onto `(0, 1)`.
3. For every `β ∈ (0, 1)`, every coefficient smaller than `δ(β)` is refuted by a bounded pair.
4. `δ` is strictly increasing, strictly convex and differentiable on `(0, 1)`; its derivative tends
   to `0` at `0⁺` and to `+∞` at `1⁻`, and ranges over `(0, ∞)`.
5. (12) `κ(C)` is strictly increasing and a bijection from `(1/4, 1/2)` onto `(0, ∞)`.
6. (13) `ρ(κ(C)) = 1/(S(C) + u) = 1/(1 + C I(C))`: the bound holds on every admissible pair with
   `M > 0`, `G/M = κ(C)`, and bounded pairs with exactly `G/M = κ(C)` approach it.
7. (14) For every `κ > 0`, `κ ρ(κ)` is the least upper bound of `κβ − δ(β)` over `0 < β < 1`.

**Formalization Note.** Pairs are the published `IsAdmissiblePair` laws; `M`, `G`, `Γ_max` the
published `sellerMean`, `firstBestGFT`, `gammaMax`; `S`, `τ`, `I` the published `SCurve`,
`tauCurve`, `Ical`. Because `δ` and `ρ` are infima, the bound and the refutation are stated as
well as the value. "Extending `δ` by `+∞` outside `(0, 1)`" only restricts the supremum in (14) to
`0 < β < 1`, which is written as `IsLUB`. Since `κ` is onto `(0, ∞)`, the approach clause stated
for every `C` covers every fixed `κ > 0`. -/
theorem theorem_B :
    (∀ C ∈ Ioo (1 / 4 : ℝ) (1 / 2),
      (∀ μs μb : Measure ℝ, IsAdmissiblePair μs μb →
        betaC C * firstBestGFT μs μb - tauCurve C / SCurve C * sellerMean μs ≤ gammaMax μs μb) ∧
      (∀ δ' : ℝ, δ' < tauCurve C / SCurve C → ∃ μs μb : Measure ℝ,
        IsAdmissiblePair μs μb ∧ IsBoundedPair μs μb ∧
        gammaMax μs μb < betaC C * firstBestGFT μs μb - δ' * sellerMean μs) ∧
      deltaSharp (betaC C) = tauCurve C / SCurve C) ∧
    betaC '' Ioo (1 / 4 : ℝ) (1 / 2) = Ioo 0 1 ∧
    (∀ β ∈ Ioo (0 : ℝ) 1, ∀ δ' : ℝ, δ' < deltaSharp β → ∃ μs μb : Measure ℝ,
      IsAdmissiblePair μs μb ∧ IsBoundedPair μs μb ∧
      gammaMax μs μb < β * firstBestGFT μs μb - δ' * sellerMean μs) ∧
    StrictMonoOn deltaSharp (Ioo 0 1) ∧
    StrictConvexOn ℝ (Ioo 0 1) deltaSharp ∧
    DifferentiableOn ℝ deltaSharp (Ioo 0 1) ∧
    Tendsto (deriv deltaSharp) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (deriv deltaSharp) (𝓝[<] 1) atTop ∧
    deriv deltaSharp '' Ioo 0 1 = Ioi 0 ∧
    StrictMonoOn kappaC (Ioo (1 / 4) (1 / 2)) ∧
    BijOn kappaC (Ioo (1 / 4) (1 / 2)) (Ioi 0) ∧
    (∀ C ∈ Ioo (1 / 4 : ℝ) (1 / 2),
      rhoCond (kappaC C) = 1 / (SCurve C + uC C) ∧
      1 / (SCurve C + uC C) = 1 / (1 + C * Ical C) ∧
      (∀ μs μb : Measure ℝ, IsAdmissiblePair μs μb → 0 < sellerMean μs →
        firstBestGFT μs μb = kappaC C * sellerMean μs →
        1 / (SCurve C + uC C) ≤ gammaMax μs μb / firstBestGFT μs μb) ∧
      (∀ ε : ℝ, 0 < ε → ∃ μs μb : Measure ℝ,
        IsAdmissiblePair μs μb ∧ IsBoundedPair μs μb ∧ 0 < sellerMean μs ∧
        firstBestGFT μs μb = kappaC C * sellerMean μs ∧
        gammaMax μs μb / firstBestGFT μs μb < 1 / (SCurve C + uC C) + ε)) ∧
    (∀ κ : ℝ, 0 < κ →
      IsLUB ((fun β => κ * β - deltaSharp β) '' Ioo 0 1) (κ * rhoCond κ)) := by sorry

end FixedPriceTrade.Supplement
