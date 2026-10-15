-- Prove2me | Theorems.Thm_AdvanceSales_Pricing_proposition_20
-- name    : AdvanceSales.Pricing.proposition_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:55.266726+00:00
-- url     : https://prove2.me/theorems/e837cb2b-27ae-404f-9772-c0c8eac1a9ae
-- title:
--   Proposition 20 — three candidate prices and their regional profits
-- statement:
--   The paper's candidate prices and associated profits are
--
--   $$p_2=v-\frac{\ln v}{1-1/v},\quad \pi_2=v-1-\ln v;\qquad p_3=v-k-1,\quad \pi_3=(v-k-1)(1-e^{-(W+k+1)});\qquad p_4=v-k-\frac{\ln(v-k)}{1-1/(v-k)},\quad \pi_4=v-k-1-\ln(v-k).$$
--
--   Among equilibria with no early arrivals, profit is at most $\pi_2$ when $v>1$; if $p_2$ lies in Region 2 and is nonnegative, it attains that bound with rates $(0,\ln v)$. When $v>k+1$, the boundary price $p_3$ induces $(0,W+k+1)$ and earns $\pi_3$. Among equilibria with no late arrivals, profit is at most $\pi_4$ when $v-k>1$; if $p_4$ lies in Region 4 and is nonnegative, it attains that bound with rates $(\ln(v-k),0)$.
--
--   These candidates reduce the global price comparison to the regional maxima and one boundary.
--
--   **Formalization Note** The printed list says “$p_2,p_4$ and $p$”; the displayed equations identify these as $p_2,p_3,p_4$. The regional bounds also include the zero-arrival boundary, where they remain valid.
-- source:
--   Glazer, Hassin, Nowik, How Advance Sales Can Reduce Profits, arXiv:1912.02869v2, pp. 38–39, Proposition 20, (39)–(41)

import Mathlib
import Definitions.Def_AdvanceSales_Pricing_Setting

namespace AdvanceSales.Pricing

theorem proposition_20 (v k : ℝ) (hk : 0 < k) :
    (1 < v →
      (∀ p x y : ℝ, 0 ≤ p → IsEq v k p x y → x = 0 →
        profit p x y ≤ pi2 v) ∧
      (0 ≤ p2 v → v - k - 1 ≤ p2 v → p2 v ≤ v - 1 →
        IsEq v k (p2 v) 0 (Real.log v) ∧
        profit (p2 v) 0 (Real.log v) = pi2 v)) ∧
    (k + 1 < v →
      IsEq v k (p3 v k) 0 (Wk k + k + 1) ∧
      profit (p3 v k) 0 (Wk k + k + 1) = pi3 v k) ∧
    (1 < v - k →
      (∀ p x y : ℝ, 0 ≤ p → IsEq v k p x y → y = 0 →
        profit p x y ≤ pi4 v k) ∧
      (0 ≤ p4 v k → p4 v k ≤ v - vOf k →
        IsEq v k (p4 v k) (Real.log (v - k)) 0 ∧
        profit (p4 v k) (Real.log (v - k)) 0 = pi4 v k)) := by sorry

end AdvanceSales.Pricing
