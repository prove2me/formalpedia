-- Prove2me | Theorems.Thm_AlliancePortfolio_Sharing_proposition_1
-- name    : AlliancePortfolio.Sharing.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:48.74034+00:00
-- url     : https://prove2.me/theorems/e200d512-645d-4c3c-8fbf-bb0934fd1e47
-- title:
--   Proposition 1, p. 10 — both firms find knowledge sharing privately profitable iff V − I ≥ |π_F − π_A|
-- statement:
--   Consider a single alliance between firms $F$ and $A$ with alliance value $V$, ex post outside options $\pi_F$ and $\pi_A$ satisfying $V \ge \pi_F + \pi_A$, and total knowledge-sharing cost $I > 0$, each firm paying $\tfrac12 I$. Firm $i$'s Nash-bargaining payoff is $\Pi_i = \pi_i + \tfrac12[V - \pi_F - \pi_A] - \tfrac12 I$, and knowledge sharing is privately profitable for $i$ when $\Pi_i \ge 0$.
--
--   Then knowledge sharing is privately profitable for both firms if and only if
--
--   $$V - I \ge |\pi_F - \pi_A| .$$
--
--   The result says that value creation ($V \ge I$, the efficiency condition) is not enough: shifts in bargaining positions caused by knowledge sharing, measured by $|\pi_F - \pi_A|$, can lead to underinvestment.
--
--   **Formalization Note** Proposition 1 also says knowledge sharing "is efficient when $V \ge I$"; that sentence is the paper's definition of efficiency and is not part of the formal statement. The paper writes "only when"; the constraint-level statement is an equivalence, because the paper rewrites the two constraints (2) equivalently as (3) and (4) on p. 9. The standing assumptions $I > 0$ and $V \ge \pi_F + \pi_A$ of §2 are kept as hypotheses.
-- source:
--   Arora, Belenzon & Patacconi, Knowledge sharing in alliances and alliance portfolios, author manuscript of January 24, 2020 (Management Science 2021, doi:10.1287/mnsc.2020.3614), p. 10, Proposition 1 (eq. (5)); pp. 7–9, eq. (1)–(4)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_AlliancePortfolio_Sharing_Model

namespace AlliancePortfolio.Sharing

theorem proposition_1 (V I πF πA : ℝ) (hI : 0 < I) (hV : πF + πA ≤ V) :
    SingleFeasible V I πF πA ↔ |πF - πA| ≤ V - I := by sorry

end AlliancePortfolio.Sharing
