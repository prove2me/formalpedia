-- Prove2me | Theorems.Thm_BrandSpillover_Commitment_appendix_b_quantities
-- name    : BrandSpillover.Commitment.appendix_b_quantities
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:54.787993+00:00
-- url     : https://prove2.me/theorems/6e13bbc0-1fcd-41b1-816a-6551ff511aeb
-- title:
--   Appendix B, p. 41 — equilibrium quantities under (O, I) and (O, O), and their signs
-- statement:
--   Assume the standing assumptions and a spillover level $a \in [0,1]$.
--
--   1. Under $(O,I)$, at the CM's optimal price: if $c \le c^{oi}$ then $q^{oi}_S = \frac{2-\theta-c}{3}$ and $q^{oi}_W = \frac{2\theta-1-c}{3}$; if $c > c^{oi}$ then $q^{oi}_S = \frac{2-\theta+c}{6}$ and $q^{oi}_W = \frac{7\theta-2-7c}{12}$. In both cases $q^{oi}_S > 0$ and $q^{oi}_W \ge 0$.
--   2. Under $(O,O)$, at the CM's optimal prices:
--   $$\big(q^{oo}_S, q^{oo}_W\big) = \begin{cases} \big(\tfrac{2-\theta-c+a-a\theta}{3},\ \tfrac{4\theta-2-2c-a+a\theta}{6}\big) & c \le c^{oo}_1,\\[2pt] \big(\tfrac{7-6c-2\theta+a-a\theta}{12},\ \tfrac{2\theta-1+2a-2a\theta}{6}\big) & c^{oo}_1 < c \le c^{oo}_2,\\[2pt] \big(\tfrac{2-a-\theta+a\theta}{6},\ \tfrac{2\theta-1+2a-2a\theta}{6}\big) & c > c^{oo}_2,\end{cases}$$
--   and both quantities are strictly positive.
--
--   These are the quantities that justify the lower bound $\underline\theta$ on Firm W's brand power: under it, no firm is driven out of the market.
--
--   **Formalization Note** The paper states $q^{oi}_W > 0$ under $\theta > \underline\theta$; the model section assumes $\theta \ge \underline\theta$, and at $\theta = (1+c)/2$ with $c \le c^{oi}$ the quantity is $0$, so the statement asserts $q^{oi}_W \ge 0$.
-- source:
--   Wu, Zhang & Zhou, Brand Spillover as a Marketing Strategy, SSRN preprint 3891915 (June 2021), p. 41, Appendix B

import Mathlib
import Definitions.Def_BrandSpillover_Commitment_Model

namespace BrandSpillover.Commitment

/-- Appendix B, p. 41: the firms' quantities at the CM's optimal prices under `(O, I)` and
`(O, O)`, and their signs. Under `(O, I)` Firm W's quantity is only nonnegative, since
`θ ≥ θ̲` allows `θ = (1 + c)/2`. -/
theorem appendix_b_quantities (P : Params) (hP : P.Standing) (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) :
    (∀ w : ℝ × ℝ, IsOptPrices P a .OI w →
      (P.c ≤ cOI P → quantS P a .OI w = (2 - P.θ - P.c) / 3 ∧
          quantW P a .OI w = (2 * P.θ - 1 - P.c) / 3) ∧
      (cOI P < P.c → quantS P a .OI w = (2 - P.θ + P.c) / 6 ∧
          quantW P a .OI w = (7 * P.θ - 2 - 7 * P.c) / 12) ∧
      0 < quantS P a .OI w ∧ 0 ≤ quantW P a .OI w) ∧
    (∀ w : ℝ × ℝ, IsOptPrices P a .OO w →
      (P.c ≤ cOO1 P a → quantS P a .OO w = (2 - P.θ - P.c + a - a * P.θ) / 3 ∧
          quantW P a .OO w = (4 * P.θ - 2 - 2 * P.c - a + a * P.θ) / 6) ∧
      (cOO1 P a < P.c → P.c ≤ cOO2 P a →
          quantS P a .OO w = (7 - 6 * P.c - 2 * P.θ + a - a * P.θ) / 12 ∧
          quantW P a .OO w = (2 * P.θ - 1 + 2 * a - 2 * a * P.θ) / 6) ∧
      (cOO2 P a < P.c → quantS P a .OO w = (2 - a - P.θ + a * P.θ) / 6 ∧
          quantW P a .OO w = (2 * P.θ - 1 + 2 * a - 2 * a * P.θ) / 6) ∧
      0 < quantS P a .OO w ∧ 0 < quantW P a .OO w) := by sorry

end BrandSpillover.Commitment
