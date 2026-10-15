-- Prove2me | Theorems.Thm_EndogMerger_SymLoyal_proposition_2
-- name    : EndogMerger.SymLoyal.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:55.071166+00:00
-- url     : https://prove2.me/theorems/ce9530d7-0140-45fc-aba5-fff6ec4e008e
-- title:
--   Proposition 2, PDF p. 18 — L^(AB) ≥ L^(BC) ≥ L^(0) for all α < k < 1
-- statement:
--   Let $0<\alpha<1/3$, $\alpha<k<1$ and $r>0$. The Table A1 lower bounds of price support in the three structures satisfy
--   $$
--   L^{(AB)}\ \ge\ L^{(BC)}\ \ge\ L^{(0)} .
--   $$
--
--   Mergers soften price competition: the lower bound of the price support is highest under the mixed merger and lowest without merger.
--
--   **Formalization Note** "For all ranges of $k$" is rendered as $\alpha<k<1$, the range of Table A1. $0<\alpha$ and $r>0$ are added.
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, PDF p. 18, Proposition 2; proof PDF pp. 47–48

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting

namespace EndogMerger.SymLoyal
theorem proposition_2 (α k r : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k)
    (hk1 : k < 1) (hr : 0 < r) :
    L0 α k r ≤ LBC α k r ∧ LBC α k r ≤ LAB α k r := by sorry
end EndogMerger.SymLoyal
