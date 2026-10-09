-- Prove2me | Theorems.Thm_BalancedPrices_ClosureMax_closure_max_b
-- name    : BalancedPrices.ClosureMax.closure_max_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:26.865075+00:00
-- url     : https://prove2.me/theorems/940b3468-1591-430d-a9e3-42252bbc8787
-- title:
--   Proof of Theorem 5.3, p. 560 — property (b) for the supporting profile's prices
-- statement:
--   Fix agents with outcome spaces $X_i$ (null outcome $\varnothing$), a downward-closed feasible set $\mathcal F$, an exchange-compatible family $(\mathcal F_x)_{x\in X}$, base valuation spaces $V_i$ whose functions take values in $[0,1]$, and constants $\alpha>0$, $\beta\ge0$. Let ALG be a consistent allocation rule feasible for every profile in $V^{\max}$, and suppose that for every $w\in V$ the pricing rule $p^w$ is $(\alpha,\beta)$-balanced with respect to $w$, ALG and $(\mathcal F_x)$. Let $v\in V^{\max}$ and let $\tilde v\in V$ be a supporting valuation profile for $\operatorname{ALG}(v)$. Then for every $x\in\mathcal F$ and every $x'\in\mathcal F_x$,
--   $$\sum_{i}p_i^{\tilde v}(x'_i\mid x_{[i-1]})\le\beta\cdot v(\operatorname{OPT}(v,\mathcal F_x)).$$
--
--   This is property (b) of Definition 3.1 for the pricing rule $p^{\tilde v}$ with respect to $v$, the second half of Theorem 5.3.
--
--   **Formalization Note** Agents are indexed from zero. The price sum stays in `ℝ≥0∞` and the real bound is embedded by `ENNReal.ofReal`, so an infinite price never satisfies the bound. The optimum over an empty $\mathcal F_x$ is $0$.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 560, proof of Theorem 5.3, property (b)

import Mathlib
import Definitions.Def_BalancedPrices_ClosureMax_Composition

namespace BalancedPrices.ClosureMax

/-- Property (b) in the proof of Theorem 5.3. -/
theorem closure_max_b {n : ℕ} {X : Fin n → Type*}
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
    (x x' : BalancedPrices.Extension.Outcome X) (hx : x ∈ F) (hx' : x' ∈ Fam x) :
    (∑ i, pr vt i (x' i) (BalancedPrices.Extension.pre nul x i)) ≤
      ENNReal.ofReal (β * BalancedPrices.Extension.optVal vf (Fam x)) := by sorry

end BalancedPrices.ClosureMax
