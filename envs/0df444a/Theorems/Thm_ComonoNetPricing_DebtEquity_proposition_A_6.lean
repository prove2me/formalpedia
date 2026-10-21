-- Prove2me | Theorems.Thm_ComonoNetPricing_DebtEquity_proposition_A_6
-- name    : ComonoNetPricing.DebtEquity.proposition_A_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:47.995982+00:00
-- url     : https://prove2.me/theorems/0605b53b-8490-4ff7-b889-c5057545a60b
-- title:
--   Proposition A.6, p. 36 — the greatest clearing wealth V, payments p and equity E are nondecreasing in the endowments
-- statement:
--   For a positive integer $n$, consider the Rogers–Veraart network under the standing assumptions, with greatest clearing wealth $V(x)$, payments $p(x) = \bar p - V(x)^-$ and equity $E(x) = V(x)^+$ (Definition 2.2). For endowments $0 \le x \le y$ (componentwise),
--   $$V(x) \le V(y), \qquad p(x) \le p(y), \qquad E(x) \le E(y).$$
--
--   Monotonicity in the endowments is what makes the default regions of a comonotonic endowment $f(q)$ intervals in $q$.
-- source:
--   Banerjee & Feinstein, Pricing of debt and equity in a financial network with comonotonic endowments, arXiv:1810.01372v5, p. 36, Proposition A.6

import Mathlib
import Definitions.Def_ComonoNetPricing_DebtEquity_Network

namespace ComonoNetPricing.DebtEquity

open Matrix

/-- Proposition A.6, p. 36: the greatest clearing wealth `V`, the payments `p` and the equity
`E` of Definition 2.2 are nondecreasing in the endowments `x ∈ ℝⁿ₊`. -/
theorem proposition_A_6 {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing) (x y : Fin n → ℝ)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    N.clearingWealth x ≤ N.clearingWealth y ∧ N.payment x ≤ N.payment y ∧
      N.equity x ≤ N.equity y := by sorry

end ComonoNetPricing.DebtEquity
