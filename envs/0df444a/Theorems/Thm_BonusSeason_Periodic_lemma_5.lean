-- Prove2me | Theorems.Thm_BonusSeason_Periodic_lemma_5
-- name    : BonusSeason.Periodic.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:02.133532+00:00
-- url     : https://prove2.me/theorems/5d5a27ec-f3a4-4c4d-b73f-56dfc8bea574
-- title:
--   Lemma 5, pp. 26–27 (PDF 27–28) — an incentive-compatible periodic contract with present values P₁ and P₂ exists
-- statement:
--   Under the hypotheses of Lemma 3, there is a periodic contract $\{b^s_1,b^s_2,w_1,w_2\}$ that satisfies the incentive constraints (32), (35), (36) — equivalently (37)–(39) — whose present value is $P_1$ for a worker hired in an odd period and $P_2$ for a worker hired in an even period.
--
--   Periodic quitting can therefore always be implemented by a contract that delivers the bargained pay.
--
--   **Formalization Note** One contract serves both hiring parities, as the paper's contract $\{b^s_1,b^s_2,w_1,w_2\}$ does: the bonus depends on the hiring period, the wages do not.
-- source:
--   Van Wesep & Waters, Bonus season: A theory of periodic labor markets and coordinated bonuses, SSRN 3124536 (version of January 13, 2021), pp. 26–27 (PDF 27–28), Lemma 5

import Mathlib
import Definitions.Def_BonusSeason_Periodic_Model

namespace BonusSeason.Periodic

/-- Lemma 5, pp. 26–27: there is a periodic contract that satisfies the incentive constraints
and has present value `P₁` for an odd-period hire and `P₂` for an even-period hire. -/
theorem lemma_5 (P : Params) (hP : P.Standing) (m : ℝ → ℝ → ℝ) (hm : MatchingA1 m)
    (L : MarketState) (hL : L.Solves P m) (X : Values) (hX : X.Solves P L m) :
    ∃ c : PeriodicContract, IncentiveCompatible P X c ∧ pvOdd P c = X.P₁ ∧ pvEven P c = X.P₂ := by sorry
end BonusSeason.Periodic
