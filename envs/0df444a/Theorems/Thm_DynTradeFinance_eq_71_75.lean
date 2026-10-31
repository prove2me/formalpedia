-- Prove2me | Theorems.Thm_DynTradeFinance_eq_71_75
-- name    : DynTradeFinance.eq_71_75
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:34.925479+00:00
-- url     : https://prove2.me/theorems/77a77133-77df-4b7d-a81c-57905832792b
-- title:
--   Eqs. (71)–(75), p. 41 — the cross derivatives of $\partial V/\partial\bar d$ in $p_1$, $l_2-l_1$, $\mu$, $\delta$ (corrected: sign in (73); $\delta<\min(\mu,1)$)
-- statement:
--   Let $0<p_1<1$, $l_1<l_2$, $0<\delta<\min(\mu,1)$ and $\bar d>0$; write $A=l_2-l_1$ and $B=1+(\mu-\delta)\bar d$. Regard the right side of (69),
--   $$h(p,a,m,s)=-\frac{p\,a\,s}{(1-s)[1+(m-s)\bar d]^2},$$
--   as a function of $(p_1,\,l_2-l_1,\,\mu,\,\delta)$. At $(p_1,A,\mu,\delta)$ its partial derivatives are
--
--   1. (71) $\displaystyle\frac{\partial h}{\partial p}=-\frac{A\,\delta}{(1-\delta)B^2}<0$;
--   2. (72) $\displaystyle\frac{\partial h}{\partial a}=-\frac{p_1\,\delta}{(1-\delta)B^2}<0$;
--   3. (73) $\displaystyle\frac{\partial h}{\partial m}=\frac{p_1A\cdot2\delta\bar d}{(1-\delta)B^3}>0$;
--   4. (75) $\displaystyle\frac{\partial h}{\partial s}=-\,p_1A\,\frac{(1-\delta)B+\delta\,[B+2\bar d(1-\delta)]}{(1-\delta)^2B^3}<0$.
--
--   These signs say that reducing the information delay is worth more when $p_1$ and $l_2-l_1$ are high, $\mu$ is small and $\delta$ is high.
--
--   Differences from the source:
--   - correction: ∂²V/∂d∂µ = p₁(l₁ − l₂)·2δd/((1 − δ)[1 + (µ − δ)d]³) > 0 (73) → p₁(l₂ − l₁)·2δd̄/((1 − δ)[1 + (µ − δ)d̄]³) > 0; reason: the printed right side is negative (l₁ < l₂) and contradicts its own '> 0'; at p₁ = 1/2, l₁ = 0, l₂ = 1/2, µ = 1/2, δ = 1/4, d = 1 the derivative is 32/375 against the printed −32/375
--   - reading: (74), an intermediate expression for ∂²V/∂d∂δ printed with an unbalanced bracket → not restated; the derivative in δ is stated in the simplified form (75); reason: (74) is the unsimplified form of (75); as printed it is not a well-formed expression
--   - correction: δ ≤ min(µ, 1) (p. 11) → 0 < δ, δ < µ and δ < 1; reason: at equality the expected capital cost is infinite and (7), (9), (10) divide by µ − δ = 0: δ = µ = 1/2, p₁ = p₂ = 1/2, l₁ = 0, l₂ = 1/2, c = 1, w = 2, λ = 1 meets every assumption of §§3–4, yet E[e^{δ(T̃₁+T̃₂)}] = ∞ since T̃₂ ∼ Exp(1/2); footnote 15 states the assumption is there to keep the expected financing cost finite
--   - reading: p₁ is a probability, with 'p₁, p₂ < 1' in the proof of Proposition 1 (p. 38); no lower bound is stated → 0 < p₁ < 1; reason: the range of p₁ in the model; p₁ > 0 is what makes the signs strict
--   - generalization: d = 1/λ with λ > µ, i.e. d ∈ (0, 1/µ), under all standing assumptions → every d̄ > 0, with hypotheses only on p₁, l₁, l₂, µ, δ; reason: the identities and signs hold for every d̄ > 0; the statement specializes to d̄ ∈ (0, 1/µ)
--   - encoding: the partial derivatives ∂²V/∂d∂p₁, ∂d∂(l₂ − l₁), ∂d∂µ, ∂d∂δ → HasDerivAt of h in one argument with the others fixed; the derivative in l₂ − l₁ is taken in a variable a at a = l₂ − l₁; reason: the same partial derivatives
-- source:
--   Lee, Tang, Yang, Zhang, Dynamic trade finance in the presence of information frictions and FinTech, SSRN 3632563 (Feb. 2022 revision), proof of Proposition 3, Eqs. (71)–(75), p. 41

import Mathlib

namespace DynTradeFinance

/-- **Cross derivatives of the marginal value of delay, Eqs. (71)–(75)** (proof of Proposition 3),
Lee, Tang, Yang, Zhang, SSRN 3632563, p. 41: "For cross derivatives:
∂²V/∂d∂p₁ = −(l₂ − l₁) δ/((1 − δ)[1 + (µ − δ)d]²) < 0; (71)
∂²V/∂d∂(l₂ − l₁) = −p₁ δ/((1 − δ)[1 + (µ − δ)d]²) < 0; (72)
∂²V/∂d∂µ = p₁(l₁ − l₂) 2δd/((1 − δ)[1 + (µ − δ)d]³) > 0; (73)
∂²V/∂d∂δ = −p₁(l₂ − l₁) ((1 − δ)[1 + (µ − δ)d] + δ[1 + (µ − δ)d + 2d(1 − δ)])/((1 − δ)²[1 + (µ − δ)d]³) < 0 (75)."

Let `0 < p₁ < 1`, `l₁ < l₂`, `0 < δ < min(μ, 1)`, `d̄ > 0`, and write `A = l₂ − l₁`,
`B = 1 + (μ − δ)d̄`. Let `h(p, a, m, s) := −p·a·s/((1 − s)[1 + (m − s)d̄]²)` be the right side
of (69) as a function of `(p₁, l₂ − l₁, μ, δ)`. Then at `(p₁, A, μ, δ)`:
1. (71) `∂h/∂p = −Aδ/((1 − δ)B²) < 0`;
2. (72) `∂h/∂a = −p₁δ/((1 − δ)B²) < 0`;
3. (73, corrected) `∂h/∂m = p₁A·2δd̄/((1 − δ)B³) > 0`;
4. (75) `∂h/∂s = −p₁A((1 − δ)B + δ(B + 2d̄(1 − δ)))/((1 − δ)²B³) < 0`.

**Formalization Note.** The printed (73) has the factor `p₁(l₁ − l₂)`, which makes its right side
negative and contradicts its own "> 0"; the corrected value `p₁(l₂ − l₁)·2δd̄/…` is stated. (74)
is an unsimplified form of (75) and is not restated. Each partial derivative is a `HasDerivAt`
of `h` in one argument with the others fixed. -/
theorem eq_71_75 (p₁ l₁ l₂ μ δ dbar : ℝ) (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hl : l₁ < l₂)
    (hδ : 0 < δ) (hδμ : δ < μ) (hδ1 : δ < 1) (hdbar : 0 < dbar) :
    HasDerivAt (fun p : ℝ => -(p * (l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2)))
      (-((l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2))) p₁ ∧
    -((l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2)) < 0 ∧
    HasDerivAt (fun a : ℝ => -(p₁ * a * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2)))
      (-(p₁ * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2))) (l₂ - l₁) ∧
    -(p₁ * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2)) < 0 ∧
    HasDerivAt (fun m : ℝ => -(p₁ * (l₂ - l₁) * δ / ((1 - δ) * (1 + (m - δ) * dbar) ^ 2)))
      (p₁ * (l₂ - l₁) * (2 * δ * dbar) / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 3)) μ ∧
    0 < p₁ * (l₂ - l₁) * (2 * δ * dbar) / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 3) ∧
    HasDerivAt (fun s : ℝ => -(p₁ * (l₂ - l₁) * s / ((1 - s) * (1 + (μ - s) * dbar) ^ 2)))
      (-(p₁ * (l₂ - l₁) * ((1 - δ) * (1 + (μ - δ) * dbar) +
          δ * (1 + (μ - δ) * dbar + 2 * dbar * (1 - δ))) /
        ((1 - δ) ^ 2 * (1 + (μ - δ) * dbar) ^ 3))) δ ∧
    -(p₁ * (l₂ - l₁) * ((1 - δ) * (1 + (μ - δ) * dbar) +
          δ * (1 + (μ - δ) * dbar + 2 * dbar * (1 - δ))) /
        ((1 - δ) ^ 2 * (1 + (μ - δ) * dbar) ^ 3)) < 0 := by sorry

end DynTradeFinance
