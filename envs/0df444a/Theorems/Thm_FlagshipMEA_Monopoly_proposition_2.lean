-- Prove2me | Theorems.Thm_FlagshipMEA_Monopoly_proposition_2
-- name    : FlagshipMEA.Monopoly.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:08:43.353079+00:00
-- url     : https://prove2.me/theorems/b6fa5a6d-12c4-4f61-9b1f-9f104add1022
-- title:
--   Proposition 2 — positively marketed products maximize the MEA index
-- statement:
--   Let $m$ solve the firm's profit maximization problem (8), and write $M=\sum_j m_j$ for its total marketing effort. If product $i$ receives positive effort, then its MEA index is maximal at that total:
--
--   $$m_i>0\quad\Longrightarrow\quad i\in\operatorname*{arg\,max}_j R_j(M).$$
--
--   This necessary condition connects the products selected by an optimal allocation to their revenue index. **Formalization Note** Positive effort automatically makes $M>0$, the domain of Definition 2.
-- source:
--   He, Ke & Zhang, A Model of Product Line Marketing, SSRN 3631879 (version of August 2021), pp. 14–15 (PDF 16–17), Proposition 2, (14)

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_Model

namespace FlagshipMEA.Monopoly

/-- Proposition 2 (pp. 14–15): any product receiving positive effort in an
optimal strategy maximizes the MEA index at the strategy's total effort. -/
theorem proposition_2 {n : ℕ} (D : Data n) (hS : D.Standing)
    (hfc : D.FcConcave) (m : Fin n → ℝ) (hm : D.IsOptimal m)
    (i : Fin n) (hi : 0 < m i) : D.IsArgmaxR (tme m) i := by sorry

end FlagshipMEA.Monopoly
