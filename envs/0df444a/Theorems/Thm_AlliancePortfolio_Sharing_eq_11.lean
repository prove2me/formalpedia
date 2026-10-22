-- Prove2me | Theorems.Thm_AlliancePortfolio_Sharing_eq_11
-- name    : AlliancePortfolio.Sharing.eq_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:49:31.001998+00:00
-- url     : https://prove2.me/theorems/28f45fb5-9155-4ed5-904b-9e1b4b0257ac
-- title:
--   Equation (11), p. 24 — Π_A, Π_B ≥ 0 iff V − I − π_F + (2/3)b − (1/3)(s^Imp − s^RB) ≥ 0
-- statement:
--   In the alliance portfolio with players $\{F, A, B\}$, let $\varphi_A, \varphi_B$ be the Shapley values of the Table 1 game and let the net payoffs of the partners be $\Pi_A = \varphi_A - \tfrac12 I$ and $\Pi_B = \varphi_B - \tfrac12 I$, where $\tfrac12 I$ is each partner's knowledge-sharing cost.
--
--   Then the knowledge-sharing constraints of both "weak" partners hold if and only if
--
--   $$\Pi_A \ge 0 \text{ and } \Pi_B \ge 0 \iff V - I - \pi_F + \tfrac23 b - \tfrac13\bigl(s^{Imp} - s^{RB}\bigr) \ge 0 .$$
--
--   This condition drives the comparative statics of Proposition 5 and the lower end of the interval in Proposition 6.
--
--   **Formalization Note** The equivalence holds for all real parameters, so no hypotheses are needed.
-- source:
--   Arora, Belenzon & Patacconi, Knowledge sharing in alliances and alliance portfolios, author manuscript of January 24, 2020 (Management Science 2021, doi:10.1287/mnsc.2020.3614), p. 24, equation (11)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_AlliancePortfolio_Sharing_Model

namespace AlliancePortfolio.Sharing

theorem eq_11 (V I b πF sImp sRB : ℝ) :
    (0 ≤ netPayoff V I b πF sImp sRB A ∧ 0 ≤ netPayoff V I b πF sImp sRB B) ↔
      0 ≤ V - I - πF + (2 / 3) * b - (1 / 3) * (sImp - sRB) := by sorry

end AlliancePortfolio.Sharing
