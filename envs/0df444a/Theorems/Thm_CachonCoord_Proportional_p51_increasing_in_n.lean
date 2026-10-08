-- Prove2me | Theorems.Thm_CachonCoord_Proportional_p51_increasing_in_n
-- name    : CachonCoord.Proportional.p51_increasing_in_n
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:44:19.529852+00:00
-- url     : https://prove2.me/theorems/b360734a-dfb8-4d8f-aed3-39cdc7c063ee
-- title:
--   p. 51 — the left side of (22) decreases in n, so the equilibrium total q* increases in n
-- statement:
--   Let $1 \le m < n$ and write $L_k$ for the left-hand side of (22) with $k$ retailers. Then:
--
--   1. $L_n(q) < L_m(q)$ for every $q > 0$;
--   2. for a fixed contract with $b < w < p$, if $q^*_m > 0$ solves $L_m(q^*_m) = \frac{p-w}{p-b}$ and $q^*_n > 0$ solves $L_n(q^*_n) = \frac{p-w}{p-b}$, then
--   $$q^*_m < q^*_n .$$
--
--   In particular ($m = 1$) a single retailer facing the market demand orders less than $n$ competing retailers in total: the demand-stealing effect.
--
--   **Formalization Note** The case $m = 1$ is included because the page compares with a single retailer; with one retailer, $L_1 = F$ and (22) is the newsvendor fractile. The hypotheses on the demand law are the chapter's standing assumptions (p. 7), carried by the model.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, p. 51 ("Consider how the equilibrium order quantity changes in n …")

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 51: "The left hand side of (22) is decreasing in `n`. Hence, `q*` is increasing in `n`
for fixed contractual terms: a single retailer that faces market demand `D` purchases less than
multiple retailers facing the same demand." For `1 ≤ m < n`: `L_n(q) < L_m(q)` for every
`q > 0`, and for `b < w < p` the root of (22) with `m` retailers is strictly below the root
with `n` retailers. -/
theorem p51_increasing_in_n (M : Model) (m n : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
    (∀ q : ℝ, 0 < q → M.lhs22 n q < M.lhs22 m q) ∧
      ∀ w b : ℝ, b < w → w < M.p → ∀ qm qn : ℝ, 0 < qm → 0 < qn →
        M.lhs22 m qm = (M.p - w) / (M.p - b) → M.lhs22 n qn = (M.p - w) / (M.p - b) →
        qm < qn := by sorry

end CachonCoord.Proportional
