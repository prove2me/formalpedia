-- Prove2me | Theorems.Thm_AlliancePortfolio_Sharing_proposition_6
-- name    : AlliancePortfolio.Sharing.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:49:18.921858+00:00
-- url     : https://prove2.me/theorems/03d3bb27-25f1-4a38-8ee0-2820cc909a5a
-- title:
--   Proposition 6, p. 24 — if V − I ∈ [π_F − (2/3)b + (1/3)(s^Imp − s^RB), π_F), sharing is feasible in a portfolio but not in a single alliance
-- statement:
--   Consider the alliance-portfolio model of §4.1: a focal firm $F$ with partners $A$ and $B$, alliance value $V$, total knowledge-sharing cost $I > 0$, focal outside option $\pi_F$, synergy $b \ge 0$, substitutability in implementation $s^{Imp} \in [0, V - \pi_F]$ and substitutability in rival benefits $s^{RB} \in [0, \pi_F]$, with the partners' outside options $\pi_A = \pi_B = 0$. In the portfolio, the gross payoffs $\varphi_F, \varphi_A, \varphi_B$ are the Shapley value of the Table 1 coalition game, and knowledge sharing is *feasible* when $\Pi_F = \varphi_F - I \ge 0$, $\Pi_A = \varphi_A - \tfrac12 I \ge 0$ and $\Pi_B = \varphi_B - \tfrac12 I \ge 0$. In the single $F$–$A$ alliance, knowledge sharing is *feasible* when both Nash-bargaining payoffs $\Pi_F = \pi_F + \tfrac12(V - \pi_F) - \tfrac12 I$ and $\Pi_A = \tfrac12(V - \pi_F) - \tfrac12 I$ are nonnegative.
--
--   Suppose $V \ge I$. If
--
--   $$V - I \in \Bigl[\pi_F - \tfrac23 b + \tfrac13\bigl(s^{Imp} - s^{RB}\bigr),\ \pi_F\Bigr),$$
--
--   then knowledge sharing in the portfolio is feasible, while knowledge sharing in the single alliance is not.
--
--   Adding a second partner can therefore make knowledge sharing sustainable where a single alliance fails, through synergies $b$ between the partners and substitutability $s^{RB}$ in rival benefits.
--
--   **Formalization Note** The conclusion includes the focal firm's constraint $\Pi_F \ge 0$, which the paper assumes on p. 23 "to facilitate the comparison"; under the standing ranges it is a consequence of $V \ge I$, so it is concluded, not assumed. The single alliance is the $F$–$A$ alliance of §4.1 with $\pi_A = 0$. The interval can be empty for some parameters (for instance $b = 0$ and $s^{Imp} \ge s^{RB}$); it is nonempty, for example, at $V = 1$, $I = 7/10$, $\pi_F = 1/2$, $b = 3/10$, $s^{Imp} = 1/5$, $s^{RB} = 2/5$.
-- source:
--   Arora, Belenzon & Patacconi, Knowledge sharing in alliances and alliance portfolios, author manuscript of January 24, 2020 (Management Science 2021, doi:10.1287/mnsc.2020.3614), p. 24, Proposition 6

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_AlliancePortfolio_Sharing_Model

namespace AlliancePortfolio.Sharing

theorem proposition_6 (V I b πF sImp sRB : ℝ) (hstd : Standing V I b πF sImp sRB) (hVI : I ≤ V)
    (hlo : πF - (2 / 3) * b + (1 / 3) * (sImp - sRB) ≤ V - I) (hhi : V - I < πF) :
    PortfolioFeasible V I b πF sImp sRB ∧ ¬ SingleFeasible V I πF 0 := by sorry

end AlliancePortfolio.Sharing
