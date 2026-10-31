-- Prove2me | Theorems.Thm_AlliancePortfolio_Sharing_eq_9
-- name    : AlliancePortfolio.Sharing.eq_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:50.700357+00:00
-- url     : https://prove2.me/theorems/bf85f13f-3b0b-401c-8af4-81df4eff6dea
-- title:
--   Equation (9), p. 23 — the focal firm's Shapley value φ_F = V + π_F + b/3 + (s^Imp − s^RB)/3
-- statement:
--   Let $v$ be the coalition game of Table 1 on the players $\{F, A, B\}$: $v(FAB) = 2V + b$, $v(FA) = v(FB) = V + \pi_F + s^{Imp}$, $v(F) = 2\pi_F - s^{RB}$, and $v(S) = 0$ for every coalition $S$ not containing $F$ (including $v(\emptyset) = 0$). Let $\varphi_F$ be the Shapley value of $F$ in $v$.
--
--   Then
--
--   $$\varphi_F = V + \pi_F + \tfrac13 b + \tfrac13\bigl(s^{Imp} - s^{RB}\bigr).$$
--
--   This is $F$'s gross payoff in the alliance portfolio; together with (10) it gives the net payoffs from which the knowledge-sharing constraints (11) and Proposition 6 are derived.
--
--   **Formalization Note** The identity holds for all real parameters, so no hypotheses are needed. $\varphi$ is the published Shapley value applied to the Table 1 game; the closed form is the content of the theorem.
-- source:
--   Arora, Belenzon & Patacconi, Knowledge sharing in alliances and alliance portfolios, author manuscript of January 24, 2020 (Management Science 2021, doi:10.1287/mnsc.2020.3614), p. 23, equation (9) and footnote 22

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_AlliancePortfolio_Sharing_Model

namespace AlliancePortfolio.Sharing

theorem eq_9 (V b πF sImp sRB : ℝ) :
    φ V b πF sImp sRB F = V + πF + (1 / 3) * b + (1 / 3) * (sImp - sRB) := by sorry

end AlliancePortfolio.Sharing
