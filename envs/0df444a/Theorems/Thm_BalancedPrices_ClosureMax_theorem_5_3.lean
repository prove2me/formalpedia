-- Prove2me | Theorems.Thm_BalancedPrices_ClosureMax_theorem_5_3
-- name    : BalancedPrices.ClosureMax.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:23.042592+00:00
-- url     : https://prove2.me/theorems/335b01ae-67b9-43af-a61e-2ad9157bbf3d
-- title:
--   Theorem 5.3, p. 554 — balanced prices are closed under maxima of valuations
-- statement:
--   Fix agents with outcome spaces $X_i$ (null outcome $\varnothing$), a downward-closed feasible set $\mathcal F$, an exchange-compatible family $(\mathcal F_x)_{x\in X}$, base valuation spaces $V_i$ whose functions take values in $[0,1]$, and constants $\alpha>0$, $\beta\ge0$. Let ALG be a consistent allocation rule feasible for every profile in $V^{\max}$, and suppose that for every $w\in V$ the pricing rule $p^w$ is $(\alpha,\beta)$-balanced with respect to $w$, ALG and $(\mathcal F_x)$. Let $v\in V^{\max}$ and let $\tilde v\in V$ be a supporting valuation profile for $\operatorname{ALG}(v)$. Then the pricing rule $p^{\tilde v}$ is $(\alpha,\beta)$-balanced with respect to $v$, ALG and $(\mathcal F_x)$: for every $x\in\mathcal F$ and every $x'\in\mathcal F_x$,
--   $$\sum_{i}p_i^{\tilde v}(x_i\mid x_{[i-1]})\ge\frac1\alpha\bigl(v(\operatorname{ALG}(v))-v(\operatorname{OPT}(v,\mathcal F_x))\bigr),\qquad \sum_{i}p_i^{\tilde v}(x'_i\mid x_{[i-1]})\le\beta\cdot v(\operatorname{OPT}(v,\mathcal F_x)).$$
--
--   The pricing-rule condition is retained, and the constants $\alpha$ and $\beta$ and the family $(\mathcal F_x)$ are unchanged. With Theorem 5.4 this is how balanced prices for single-item markets yield balanced prices for XOS valuations, which are maxima of additive ones.
--
--   **Formalization Note** The statement quantifies over every $v\in V^{\max}$ and every supporting $\tilde v\in V$ (not only $\tilde v=v$). Agents are indexed from zero; "for each $v\in V$ there exists a pricing rule $p^v$" is encoded as a function `pr` from profiles to pricing rules. The optimum is a real supremum, bounded by the $[0,1]$ bound of §2, which $V^{\max}$ inherits. Prices are `ℝ≥0∞` with `ENNReal.ofReal` on the real bounds. Definition 3.1 prints $\alpha>0$, $\beta\ge0$, and these are the hypotheses.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 554, Theorem 5.3; proof p. 560

import Mathlib
import Definitions.Def_BalancedPrices_ClosureMax_Composition

namespace BalancedPrices.ClosureMax

/-- Theorem 5.3: balanced prices pass to finite pointwise maxima. -/
theorem theorem_5_3 {n : ℕ} {X : Fin n → Type*}
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
    (hsup : IsSupporting Vsp vt (ALG vf) vf) :
    BalancedPrices.Extension.IsPricingRule F (pr vt) ∧
      BalancedPrices.Extension.Balanced nul α β F Fam vf (ALG vf) (pr vt) := by sorry

end BalancedPrices.ClosureMax
