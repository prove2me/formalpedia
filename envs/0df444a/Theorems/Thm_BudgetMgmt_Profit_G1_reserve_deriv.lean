-- Prove2me | Theorems.Thm_BudgetMgmt_Profit_G1_reserve_deriv
-- name    : BudgetMgmt.Profit.G1_reserve_deriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:28.655789+00:00
-- url     : https://prove2.me/theorems/a322a882-468c-4ff1-9f67-c70fd71e38d1
-- title:
--   Proof of Proposition 4.1 (reserve pricing, correlated), p. ec 42 — ∂G^R₁/∂r₁ = T·ℙ(x₁ ≥ r₁, x₋₁ ≤ r₁1⃗)(1 − ξ₁(r₁, r₁1⃗)); G^R₁ decreases on Ŝ₁
-- statement:
--   In the symmetric correlated setting, let every buyer use the same reserve price $r_1$ and let $G_1^R(r_1)=T\,\mathbb E[(r_1\vee d_1)\mathbf 1\{x_1\ge r_1\vee d_1\}]$, $d_1=\max_{i\ne1}x_i$, be one buyer's expected expenditure. Then:
--   1. for every $r_1$ with $c<r_1<\sup X_1$, $G_1^R$ is differentiable at $r_1$ and
--   $$\frac{\partial G_1^R}{\partial r_1}=T\,F_{-1}(r_1\vec1_{-1})\,\bar F_1(r_1\mid x_{-1}\le r_1\vec1_{-1})\big(1-\xi_1(r_1,r_1\vec1_{-1})\big),$$
--   where $F_{-1}(r_1\vec1_{-1})\bar F_1(r_1\mid x_{-1}\le r_1\vec 1_{-1})=\mathbb P(x_1\ge r_1,\ x_{-1}\le r_1\vec1_{-1})$;
--   2. if the distribution satisfies Assumption 1, then for every upper end $\bar r\le\sup X_1$, $\partial G_1^R/\partial r_1<0$ on the interior of $\hat S_1=\{r_1: r_1\vec1\in S'\}$ and $G_1^R$ strictly decreases on $\hat S_1$.
--
--   The sign of $1-\xi_1$ governs reserve pricing's expenditure: it increases where the generalized failure rate is below $1$ and decreases where it exceeds $1$. Part 2 gives uniqueness in Proposition 4.1 for reserve pricing; part 1 is used again in the proof of Theorem 4.2 (p. ec 46, '$G_1^R$ increases as $r_1$ increases from $c$ to $\underline s_1^R$').
--
--   **Formalization Note** The page derives the derivative on $\operatorname{int}(\hat S_1)$; the derivation does not use $r_1\in\hat S_1$, and the formula is stated on $(c,\sup X_1)$. $\xi_1$ is the model's encoding of the generalized failure rate.
--
--   Differences from the source:
--   - reading: X_i ⊆ ℝ₊ the (possibly unbounded) support of buyer i's values, 0 ∈ X_i, c ∈ int(X_i) (p. 5) → X_i = [0, v̄) with c < v̄ ≤ ∞ for every buyer; reason: the paper's proofs treat X_i as an interval (∂H/∂y₁ < 0 'as long as τ₁ ∈ int(X₁)', S_i = [c, sup X_i]); with a gap in X_i, G₁ is constant across the gap and the uniqueness of Proposition 4.1 fails, so the statements are made for interval supports; exchangeability makes all X_i equal; open versus closed upper end is a null set
--   - reading: F has a continuous and positive density f (p. 5) → f is continuous on [0, v̄)ⁿ, positive on its interior (0, v̄)ⁿ and zero outside [0, v̄)ⁿ; reason: continuity and positivity are read on the support; positivity on the null boundary faces is not required, which only weakens the hypothesis
--   - generalization: the conditional expectations E[x_i | x_{−i} ≤ z_{−i}] and E[x_i | max_{j≠i} x_j = y] are bounded (p. 5) → not assumed; only E[x_i] < ∞ is kept; reason: the paper uses these bounds only to show that large enough upper ends of the parameter spaces exist when the support is unbounded (pp. ec 7, ec 9); here the upper ends are hypotheses, and every instance of the paper satisfies the remaining assumptions
--   - encoding: ties are broken arbitrarily (p. 10) → ties are broken in favour of the lowest index; reason: ties have probability zero under a density, so every expectation is unchanged
--   - encoding: (x₁, …, x_n) has the same law as (x_σ(1), …, x_σ(n)) for every permutation σ (p. 21) → f(x ∘ σ) = f(x) for every permutation σ and every x; reason: for a density continuous on the permutation-invariant box and zero outside it, distributional exchangeability is equivalent to pointwise invariance of f
--   - encoding: T items, n buyers, buyer 1 the reference buyer → T : ℕ with 0 < T; n : ℕ with [NeZero n]; buyer 1 is index 0 : Fin n; reason: Lean indexing; the paper's T counts items and buyer 1 exists
--   - encoding: ξ_i(z_i, z_{−i}) = z_i f_i(z_i | x_{−i} ≤ z_{−i}) / F̄_i(z_i | x_{−i} ≤ z_{−i}) (p. ec 8) → z_i · ∂_t ℙ(x_i ≤ t, x_{−i} ≤ z_{−i})|_{t=z_i} / ℙ(x_i ≥ z_i, x_{−i} ≤ z_{−i}); reason: the factor ℙ(x_{−i} ≤ z_{−i}) cancels and ℙ(x_i = z_i) = 0; the ratio is evaluated only where every coordinate is positive and below v̄, where the denominator is positive
--   - reading: Assumption 1 (p. ec 9): ξ_i jointly continuous in z; ξ_i(z_i, z_i ∨ z_{−i}) strictly increasing in z_i for z_{−i} ∈ X_{−i} → continuity on the open box (0, v̄)ⁿ and strict increase for z_i ∈ (0, v̄); reason: ξ_i is undefined (0/0) where some z_j, j ≠ i, is 0; the reading on the interior is the weaker hypothesis, and at z_i = 0 the value ξ_i = 0 adds nothing
--   - encoding: S' = {r : r_i ∈ [r̲_i, r̄_i], r_i ≥ r̲_i(r_{−i})} with r̲_i(r_{−i}) the solution of ξ_i(r_i, r_i ∨ r_{−i}) = 1 and r̲_i = min r̲_i(·) ∨ c (p. ec 9) → r_i ∈ [c, r̄] and ξ_i(r_i, r_i ∨ r_{−i}) ≥ 1 whenever r_i < v̄; reason: by the page's 'ξ_i(r_i, r_i ∨ r_{−i}) ≥ 1 if r_i ≥ r̲_i(r_{−i}), and < 1 if r_i < r̲_i(r_{−i})' the two coincide under Assumption 1, and r_i ≥ r̲_i(r_{−i}) ∨ c already implies r_i ≥ r̲_i; at r_i = v̄ (bounded support) ξ's denominator vanishes and the page's constraint holds since r̲_i(r_{−i}) is interior (Claim A.4)
--   - generalization: the derivative formula is derived for r₁ ∈ int(Ŝ₁) → it is stated for every r₁ ∈ (c, v̄); reason: the derivation never uses r₁ ∈ Ŝ₁, p. ec 46 uses it on [c, s̲₁^R], and int(Ŝ₁) ⊆ (c, v̄)
--   - generalization: Ŝ₁ for the upper end r̄ chosen in the proof of Theorem 3.2 → Ŝ₁ for every r̄ with r̄ ≤ v̄; reason: the paper's r̄ lies in the support, so its Ŝ₁ is one of these
-- source:
--   Balseiro, Kim, Mahdian & Mirrokni, Budget management strategies in repeated auctions, SSRN 2858261 (version of July 8, 2020), pp. ec 41–42, proof of Proposition 4.1 (Reserve Pricing in the Correlated Setting), (B-22)

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model

namespace BudgetMgmt.Profit

open MeasureTheory

/-- Proof of Proposition 4.1 (reserve pricing in the correlated setting), p. ec 42:
`∂G^R₁/∂r₁ = T · F_{−1}(r₁1⃗_{−1}) F̄₁(r₁ | x_{−1} ≤ r₁1⃗_{−1}) (1 − ξ₁(r₁, r₁1⃗_{−1}))` at every
`r₁ ∈ (c, sup X₁)`, where `F_{−1}(r₁1⃗) F̄₁(r₁ | ·) = ℙ(x₁ ≥ r₁, x_{−1} ≤ r₁1⃗)`; and, under
Assumption 1, `∂G^R₁/∂r₁ < 0` on the interior of `Ŝ₁` and `G^R₁` strictly decreases on `Ŝ₁`. -/
theorem G1_reserve_deriv {n : ℕ} [NeZero n] (P : SymInstance n) :
    (∀ r : ℝ, P.c < r → ENNReal.ofReal r < P.vbar →
      HasDerivAt (G1 P .reserve)
        (P.T * P.law.real {x | r ≤ x 0 ∧ ∀ j, j ≠ 0 → x j ≤ r} * (1 - xi P 0 (sym r))) r) ∧
    (Assumption1 P → ∀ rbar : ℝ, ENNReal.ofReal rbar ≤ P.vbar →
      (∀ r ∈ interior (ShatR P rbar), deriv (G1 P .reserve) r < 0) ∧
      StrictAntiOn (G1 P .reserve) (ShatR P rbar)) := by sorry

end BudgetMgmt.Profit
