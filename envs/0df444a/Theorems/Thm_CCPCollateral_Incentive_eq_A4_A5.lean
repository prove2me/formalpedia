-- Prove2me | Theorems.Thm_CCPCollateral_Incentive_eq_A4_A5
-- name    : CCPCollateral.Incentive.eq_A4_A5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:09.856134+00:00
-- url     : https://prove2.me/theorems/847aeacc-7990-4bfa-9647-bc9985258dd2
-- title:
--   (A4)–(A5), proof of Proposition 2, p. 46 — no equilibrium in which some members hedge and others do not
-- statement:
--   Under the standing assumptions, let $I,F\ge 0$ with $I+F\le D$. Every pure-strategy Nash equilibrium of the hedging game is symmetric: either all $N$ members hedge or all $N$ members risk-shift.
--
--   The argument on the page compares the incentive constraints (A4) of a risk-shifting member, who faces $g$ hedgers, and (A5) of a hedging member, who faces $g-1$; they are incompatible because $X^g$ is strictly decreasing in $g$. Together with the three cases of Step 1 this yields equation (17).
--
--   **Formalization Note** Nash equilibria are weak (ties allowed), so (A4) is used in its weak form; the conclusion holds on the whole collateral region, not only in case 3.
-- source:
--   Wang, Capponi & Zhang, A Theory of Collateral Requirements for Central Counterparties, author's manuscript (2021; Management Sci. doi:10.1287/mnsc.2021.4145), proof of Proposition 2, Step 1, (A4)–(A5), p. 46

import Mathlib
import Definitions.Def_CCPCollateral_Incentive_Setting

namespace CCPCollateral.Incentive

/-- (A4)–(A5), proof of Proposition 2, Step 1 (p. 46): there is no Nash equilibrium in which some
members hedge and others do not; every Nash equilibrium is "all hedging" or "all not hedging". -/
theorem eq_A4_A5 (m : Params) (hm : Standing m) (I F : ℝ) (hI : 0 ≤ I) (hF : 0 ≤ F)
    (hIF : I + F ≤ m.D) :
    ∀ a : Fin m.N → Action, m.IsNash I F a →
      (a = fun _ => Action.s) ∨ (a = fun _ => Action.r) := by sorry

end CCPCollateral.Incentive
