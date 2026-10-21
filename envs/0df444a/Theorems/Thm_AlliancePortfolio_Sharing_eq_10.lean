-- Prove2me | Theorems.Thm_AlliancePortfolio_Sharing_eq_10
-- name    : AlliancePortfolio.Sharing.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:58.28196+00:00
-- url     : https://prove2.me/theorems/b59cbc62-a4b6-4071-a017-903836e7bfb9
-- title:
--   Equation (10), p. 23 — the partners' Shapley values φ_A = φ_B = (V − π_F)/2 + b/3 − (s^Imp − s^RB)/6
-- statement:
--   Let $v$ be the coalition game of Table 1 on the players $\{F, A, B\}$: $v(FAB) = 2V + b$, $v(FA) = v(FB) = V + \pi_F + s^{Imp}$, $v(F) = 2\pi_F - s^{RB}$, and $v(S) = 0$ for every coalition $S$ not containing $F$ (including $v(\emptyset) = 0$). Let $\varphi_A, \varphi_B$ be the Shapley values of $A$ and $B$ in $v$.
--
--   Then
--
--   $$\varphi_A = \varphi_B = \tfrac12(V - \pi_F) + \tfrac13 b - \tfrac16\bigl(s^{Imp} - s^{RB}\bigr).$$
--
--   These are the gross payoffs of the "weak" partners in the alliance portfolio; their knowledge-sharing constraints (11) follow from them.
--
--   **Formalization Note** The identity holds for all real parameters, so no hypotheses are needed. Both equalities are stated, one for $A$ and one for $B$.
-- source:
--   Arora, Belenzon & Patacconi, Knowledge sharing in alliances and alliance portfolios, author manuscript of January 24, 2020 (Management Science 2021, doi:10.1287/mnsc.2020.3614), p. 23, equation (10)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_AlliancePortfolio_Sharing_Model

namespace AlliancePortfolio.Sharing

theorem eq_10 (V b πF sImp sRB : ℝ) :
    φ V b πF sImp sRB A = (1 / 2) * (V - πF) + (1 / 3) * b - (1 / 6) * (sImp - sRB) ∧
      φ V b πF sImp sRB B = (1 / 2) * (V - πF) + (1 / 3) * b - (1 / 6) * (sImp - sRB) := by sorry

end AlliancePortfolio.Sharing
