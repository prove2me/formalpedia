-- Prove2me | Theorems.Thm_AlliancePortfolio_Sharing_single_alliance_only_if
-- name    : AlliancePortfolio.Sharing.single_alliance_only_if
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:55.239221+00:00
-- url     : https://prove2.me/theorems/e72fb440-d3ed-4bc1-84b9-e4b17afdfae9
-- title:
--   §4.1, p. 21 — in the single F–A alliance (π_A = 0), knowledge sharing is privately profitable for both only if V − I ≥ π_F
-- statement:
--   In the portfolio model of §4.1 the partners' outside options are normalised to zero. Consider the case where $F$ and $A$ share knowledge but $F$ and $B$ do not, so that $B$ plays no role and the alliance is the single alliance of §2 with $\pi_A = 0$: firm $F$'s payoff is $\Pi_F = \pi_F + \tfrac12[V - \pi_F] - \tfrac12 I$ and firm $A$'s is $\Pi_A = \tfrac12[V - \pi_F] - \tfrac12 I$. Assume $I > 0$ and $0 \le \pi_F \le V$.
--
--   If knowledge sharing is privately profitable for both firms ($\Pi_F \ge 0$ and $\Pi_A \ge 0$), then
--
--   $$V - I \ge \pi_F .$$
--
--   This is the benchmark against which the portfolio is compared in Proposition 6: when $V - I < \pi_F$, a single alliance cannot sustain knowledge sharing.
--
--   **Formalization Note** The hypotheses $0 \le \pi_F$ and $\pi_F \le V$ are the §4.1 standing ranges ($0 \le s^{RB} \le \pi_F$ and $0 \le s^{Imp} \le V - \pi_F$) restricted to the parameters that appear; $\pi_F \le V$ is also the §2 posit $V \ge \pi_F + \pi_A$ at $\pi_A = 0$. Only the "only if" direction stated on the page is formalized.
-- source:
--   Arora, Belenzon & Patacconi, Knowledge sharing in alliances and alliance portfolios, author manuscript of January 24, 2020 (Management Science 2021, doi:10.1287/mnsc.2020.3614), p. 21, §4.1 (single-alliance case)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_AlliancePortfolio_Sharing_Model

namespace AlliancePortfolio.Sharing

theorem single_alliance_only_if (V I πF : ℝ) (hI : 0 < I) (hπF : 0 ≤ πF) (hV : πF ≤ V) :
    SingleFeasible V I πF 0 → πF ≤ V - I := by sorry

end AlliancePortfolio.Sharing
