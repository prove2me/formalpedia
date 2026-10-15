-- Prove2me | Theorems.Thm_AdvanceSales_Pricing_theorem_14
-- name    : AdvanceSales.Pricing.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:57.48557+00:00
-- url     : https://prove2.me/theorems/fdd3a5e1-a014-43f4-8012-8731fa33570f
-- title:
--   Theorem 14 — four regional equilibrium formulas
-- statement:
--   Fix $k>0$ and $p\ge0$, put $z=v-p$, $v_1=z-k$, and let $v(k)$ be the regional border. In the four regions of Table 1 the unique equilibrium $(x,y)$ is, respectively,
--
--   $$(0,0),\quad (0,z+R(z)),\quad \left(v_1+R(v_1),W[A]-\left(1+\frac{k}{v_1}\right)R(v_1)\right),\quad (v_1+R(v_1),0).$$
--
--   The regions are $0\le z<1$, $1\le z\le k+1$, $k+1<z<v(k)$, and $v(k)\le z$. In each region the displayed pair characterizes every equilibrium, including existence and uniqueness there.
--
--   This gives the closed forms used to analyze profit at the regional borders.
--
--   **Formalization Note** The two printed region listings differ at boundary points. This statement uses Table 1's borders and the paper's high-demand equilibrium predicate.
-- source:
--   Glazer, Hassin, Nowik, How Advance Sales Can Reduce Profits, arXiv:1912.02869v2, p. 27, Theorem 14; p. 12, Table 1

import Mathlib
import Definitions.Def_AdvanceSales_Pricing_Setting

namespace AdvanceSales.Pricing

theorem theorem_14 (v k p : ℝ) (hk : 0 < k) (hp : 0 ≤ p) :
    (0 ≤ v - p → v - p < 1 →
      ∀ x y : ℝ, IsEq v k p x y ↔ x = 0 ∧ y = 0) ∧
    (1 ≤ v - p → v - p ≤ k + 1 →
      ∀ x y : ℝ, IsEq v k p x y ↔ x = 0 ∧ y = v - p + R (v - p)) ∧
    (k + 1 < v - p → v - p < vOf k →
      ∀ x y : ℝ, IsEq v k p x y ↔
        x = v - p - k + R (v - p - k) ∧
        y = lambertW (A v k p) - (1 + k / (v - p - k)) * R (v - p - k)) ∧
    (vOf k ≤ v - p →
      ∀ x y : ℝ, IsEq v k p x y ↔ x = v - p - k + R (v - p - k) ∧ y = 0) := by sorry

end AdvanceSales.Pricing
