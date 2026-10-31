-- Prove2me | Theorems.Thm_DynTradeFinance_eq_69_70
-- name    : DynTradeFinance.eq_69_70
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:11.936328+00:00
-- url     : https://prove2.me/theorems/4fbfc737-bd2a-48fe-a378-07e828abb742
-- title:
--   Eqs. (68)–(70), pp. 40–41 — $\partial V/\partial\bar d<0$ and $\partial^2V/\partial\bar d^2>0$ (corrected: factor $(\mu-\delta)$ in (70); $\delta<\min(\mu,1)$)
-- statement:
--   Let $0<p_1<1$, $l_1<l_2$, $0<\delta<\min(\mu,1)$, and let $\bar d>0$ be the expected information delay. Let
--   $$G(x)=p_1(l_2-l_1)\,\frac{\delta}{(1-\delta)(\mu-\delta)}\cdot\frac{1}{1+(\mu-\delta)x}.$$
--   Then
--
--   1. (68) the value of DTF (10) at $\lambda=1/\bar d$ equals $G(\bar d)$;
--   2. (69) $G$ is differentiable at $\bar d$ with
--   $$G'(\bar d)=-\,p_1(l_2-l_1)\,\frac{\delta}{(1-\delta)[1+(\mu-\delta)\bar d]^2}<0;$$
--   3. (70) the function $x\mapsto -p_1(l_2-l_1)\delta/\big((1-\delta)[1+(\mu-\delta)x]^2\big)$ is differentiable at $\bar d$ with derivative
--   $$p_1(l_2-l_1)\,\frac{2\delta(\mu-\delta)}{(1-\delta)[1+(\mu-\delta)\bar d]^3}>0.$$
--
--   So the value of DTF falls, at a decreasing rate, as the information delay grows.
--
--   Differences from the source:
--   - correction: ∂²V/∂d² = p₁(l₂ − l₁)·2δ/((1 − δ)[1 + (µ − δ)d]³) (70) → p₁(l₂ − l₁)·2δ(µ − δ)/((1 − δ)[1 + (µ − δ)d̄]³); reason: differentiating (69) produces the factor µ − δ; at p₁ = 1/2, l₁ = 0, l₂ = 1/2, µ = 1/2, δ = 1/4, d = 1 the true value is 1/4 of the printed one; the sign claim is unchanged
--   - correction: δ ≤ min(µ, 1) (p. 11) → 0 < δ, δ < µ and δ < 1; reason: at equality the expected capital cost is infinite and (7), (9), (10) divide by µ − δ = 0: δ = µ = 1/2, p₁ = p₂ = 1/2, l₁ = 0, l₂ = 1/2, c = 1, w = 2, λ = 1 meets every assumption of §§3–4, yet E[e^{δ(T̃₁+T̃₂)}] = ∞ since T̃₂ ∼ Exp(1/2); footnote 15 states the assumption is there to keep the expected financing cost finite
--   - reading: p₁ is a probability, with 'p₁, p₂ < 1' in the proof of Proposition 1 (p. 38); no lower bound is stated → 0 < p₁ < 1; reason: the range of p₁ in the model; p₁ > 0 is what makes the signs strict
--   - generalization: d = 1/λ with λ > µ, i.e. d ∈ (0, 1/µ), under all standing assumptions → every d̄ > 0, with hypotheses only on p₁, l₁, l₂, µ, δ; reason: the identities and signs hold for every d̄ > 0; the statement specializes to d̄ ∈ (0, 1/µ)
--   - encoding: ∂V/∂d and ∂²V/∂d² → HasDerivAt of the explicit functions (68) and (69) at d̄; reason: the same derivatives
-- source:
--   Lee, Tang, Yang, Zhang, Dynamic trade finance in the presence of information frictions and FinTech, SSRN 3632563 (Feb. 2022 revision), proof of Proposition 3, Eqs. (68)–(70), pp. 40–41

import Mathlib
import Definitions.Def_DynTradeFinance_ValueOfDTF

namespace DynTradeFinance

/-- **Value of DTF in the expected delay: Eqs. (68)–(70)** (proof of Proposition 3), Lee, Tang,
Yang, Zhang, SSRN 3632563, pp. 40–41: "under d = 1/λ, we re-write Eq. (67) as:
V = p₁(l₂ − l₁) δ/((1 − δ)(µ − δ)) · 1/(1 + (µ − δ)d) (68). Thus,
∂V/∂d = −p₁(l₂ − l₁) δ/((1 − δ)[1 + (µ − δ)d]²) < 0, (69) and
∂²V/∂d² = p₁(l₂ − l₁) 2δ/((1 − δ)[1 + (µ − δ)d]³) > 0. (70)"

Let `0 < p₁ < 1`, `l₁ < l₂`, `0 < δ < min(μ, 1)`, and let `d̄ > 0` be the expected information
delay. With `G(x) := p₁(l₂ − l₁)·δ/((1 − δ)(μ − δ))·1/(1 + (μ − δ)x)`:
1. (68) the closed form (10) at `λ = 1/d̄` equals `G(d̄)`;
2. (69) `G'(d̄) = −p₁(l₂ − l₁)δ/((1 − δ)[1 + (μ − δ)d̄]²)`, and this is negative;
3. (70, corrected) the derivative of the right side of (69) at `d̄` is
   `p₁(l₂ − l₁)·2δ(μ − δ)/((1 − δ)[1 + (μ − δ)d̄]³)`, and this is positive.

**Formalization Note.** The printed (70) omits the factor `(μ − δ)`; the corrected value is
stated (the sign claim is the paper's). The derivatives are `HasDerivAt` of explicit functions. -/
theorem eq_69_70 (p₁ l₁ l₂ μ δ dbar : ℝ) (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hl : l₁ < l₂)
    (hδ : 0 < δ) (hδμ : δ < μ) (hδ1 : δ < 1) (hdbar : 0 < dbar) :
    valueFormula p₁ l₁ l₂ μ (1 / dbar) δ =
      p₁ * (l₂ - l₁) * (δ / ((1 - δ) * (μ - δ))) * (1 / (1 + (μ - δ) * dbar)) ∧
    HasDerivAt (fun x : ℝ => p₁ * (l₂ - l₁) * (δ / ((1 - δ) * (μ - δ))) * (1 / (1 + (μ - δ) * x)))
      (-(p₁ * (l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2))) dbar ∧
    -(p₁ * (l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2)) < 0 ∧
    HasDerivAt (fun x : ℝ => -(p₁ * (l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * x) ^ 2)))
      (p₁ * (l₂ - l₁) * (2 * δ * (μ - δ)) / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 3)) dbar ∧
    0 < p₁ * (l₂ - l₁) * (2 * δ * (μ - δ)) / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 3) := by sorry

end DynTradeFinance
