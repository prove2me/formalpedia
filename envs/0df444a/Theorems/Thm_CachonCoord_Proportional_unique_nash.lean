-- Prove2me | Theorems.Thm_CachonCoord_Proportional_unique_nash
-- name    : CachonCoord.Proportional.unique_nash
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:44:27.991694+00:00
-- url     : https://prove2.me/theorems/b62622e9-d1c1-41ba-b5b3-7a1132262d18
-- title:
--   p. 51 — for b < w < p the game has a unique Nash equilibrium, symmetric, q*_i = q*/n with q* solving (22)
-- statement:
--   Let $n \ge 2$ retailers face a buy-back contract with $b < w < p$. There is a $q^* > 0$ solving (22),
--
--   $$
--   \frac1n F(q^*) + \left(\frac{n-1}{n}\right)\left(\frac1{q^*}\int_0^{q^*}F(x)\,dx\right) = \frac{p-w}{p-b},
--   $$
--
--   and a profile of orders is a Nash equilibrium if and only if every retailer orders $q^*_i = q^*/n$.
--
--   So the decentralized game has exactly one equilibrium, it is symmetric, and its total is the root of (22). This is the predicted outcome against which the coordinating contracts are designed.
--
--   **Formalization Note** Best responses range over all orders $x \ge 0$, so the statement also excludes equilibria in which some retailers order nothing. The hypotheses on the demand law are the chapter's standing assumptions (p. 7), carried by the model.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, p. 51 ("In other words, in this game there exists a unique Nash equilibrium …")

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 51: "when `b < w < p` … in this game there exists a unique Nash equilibrium in which the
total order quantity, `q*`, is implicitly given by (22) and each retailer's order quantity equals
`q*_i = q*/n`." There is `q* > 0` solving (22), and a profile is a Nash equilibrium if and only
if every retailer orders `q*/n`. -/
theorem unique_nash (M : Model) (n : ℕ) (hn : 2 ≤ n) (w b : ℝ) (hbw : b < w) (hwp : w < M.p) :
    ∃ qs : ℝ, 0 < qs ∧ M.lhs22 n qs = (M.p - w) / (M.p - b) ∧
      ∀ q : Fin n → ℝ, M.IsNashEq w b q ↔ ∀ i, q i = qs / n := by sorry

end CachonCoord.Proportional
