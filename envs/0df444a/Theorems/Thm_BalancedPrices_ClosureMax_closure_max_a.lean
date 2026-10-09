-- Prove2me | Theorems.Thm_BalancedPrices_ClosureMax_closure_max_a
-- name    : BalancedPrices.ClosureMax.closure_max_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:19.746999+00:00
-- url     : https://prove2.me/theorems/6957e921-6ae9-4348-b6df-7f5774176509
-- title:
--   Proof of Theorem 5.3, p. 560 — property (a) for the supporting profile's prices
-- statement:
--   Fix agents with outcome spaces $X_i$ (null outcome $\varnothing$), a downward-closed feasible set $\mathcal F$, an exchange-compatible family $(\mathcal F_x)_{x\in X}$, base valuation spaces $V_i$ whose functions take values in $[0,1]$, and constants $\alpha>0$, $\beta\ge0$. Let ALG be a consistent allocation rule feasible for every profile in $V^{\max}$, and suppose that for every $w\in V$ the pricing rule $p^w$ is $(\alpha,\beta)$-balanced with respect to $w$, ALG and $(\mathcal F_x)$. Let $v\in V^{\max}$ and let $\tilde v\in V$ be a supporting valuation profile for $\operatorname{ALG}(v)$. Then for every $x\in\mathcal F$,
--   $$\sum_{i}p_i^{\tilde v}(x_i\mid x_{[i-1]})\ge\frac1\alpha\bigl(v(\operatorname{ALG}(v))-v(\operatorname{OPT}(v,\mathcal F_x))\bigr).$$
--
--   This is property (a) of Definition 3.1 for the pricing rule $p^{\tilde v}$ with respect to $v$, the first half of Theorem 5.3.
--
--   **Formalization Note** Agents are indexed from zero. The optimum is a real supremum, bounded by the standing $[0,1]$ bound. Prices are `ℝ≥0∞`; the right-hand side enters through `ENNReal.ofReal`, which turns a negative bound into $0$, an equivalent constraint on nonnegative prices.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 560, proof of Theorem 5.3, property (a)

import Mathlib
import Definitions.Def_BalancedPrices_ClosureMax_Composition

namespace BalancedPrices.ClosureMax

/-- Property (a) in the proof of Theorem 5.3. -/
theorem closure_max_a {n : ℕ} {X : Fin n → Type*}
    (nul : BalancedPrices.Extension.Outcome X) (F : Set (BalancedPrices.Extension.Outcome X))
    (hdown : BalancedPrices.Extension.DownClosed nul F)
    (Fam : BalancedPrices.Extension.Outcome X → Set (BalancedPrices.Extension.Outcome X))
    (Vsp : ∀ i, Set (X i → ℝ))
    (hV : ∀ i (f : X i → ℝ), f ∈ Vsp i → ∀ xi, 0 ≤ f xi ∧ f xi ≤ 1)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (hFam : BalancedPrices.Extension.ExchFamily F Fam)
    (ALG : BalancedPrices.Extension.Valuation X → BalancedPrices.Extension.Outcome X)
    (hALG : ∀ w, (∀ i, w i ∈ VmaxSet Vsp i) → ALG w ∈ F)
    (hcons : Consistent Vsp ALG)
    (pr : BalancedPrices.Extension.Valuation X → BalancedPrices.Extension.PriceRule X)
    (hprice : ∀ w, (∀ i, w i ∈ Vsp i) → BalancedPrices.Extension.IsPricingRule F (pr w))
    (hbal : ∀ w : BalancedPrices.Extension.Valuation X, (∀ i, w i ∈ Vsp i) →
      BalancedPrices.Extension.Balanced nul α β F Fam w (ALG w) (pr w))
    (vf vt : BalancedPrices.Extension.Valuation X) (hvf : ∀ i, vf i ∈ VmaxSet Vsp i)
    (hsup : IsSupporting Vsp vt (ALG vf) vf)
    (x : BalancedPrices.Extension.Outcome X) (hx : x ∈ F) :
    ENNReal.ofReal ((1 / α) * (BalancedPrices.Extension.welfare vf (ALG vf) - BalancedPrices.Extension.optVal vf (Fam x))) ≤
      ∑ i, pr vt i (x i) (BalancedPrices.Extension.pre nul x i) := by sorry

end BalancedPrices.ClosureMax
