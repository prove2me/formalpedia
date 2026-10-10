-- Prove2me | Theorems.Thm_ComparativeAdvantage_ricardo_specialization_gain
-- name    : ComparativeAdvantage.ricardo_specialization_gain
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:34:48.124089+00:00
-- url     : https://prove2.me/theorems/03e40305-02e5-496a-9337-984a997d0de9
-- title:
--   Ricardo's example: specialization raises world output of both goods
-- statement:
--   In Ricardo's example England has $220$ hours of work and Portugal $170$. Then
--
--   1. producing one unit each of cloth and wine uses all of England's labour ($100+120=220$) and all of Portugal's ($90+80=170$);
--   2. if England spends its $220$ hours on cloth it produces $220/100=2.2$ units, and if Portugal spends its $170$ hours on wine it produces $170/80=2.125$ units;
--   3. both exceed the $1+1=2$ units of each good produced in autarky.
--
--   So, with specialization according to comparative advantage, the global production of both goods increases.
-- source:
--   Wikipedia, "Comparative advantage" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Comparative_advantage, section "Ricardo's example"

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

namespace ComparativeAdvantage

theorem ricardo_specialization_gain :
    england.aLC * 1 + england.aLW * 1 = england.L ∧
    portugal.aLC * 1 + portugal.aLW * 1 = portugal.L ∧
    england.L / england.aLC = 2.2 ∧ portugal.L / portugal.aLW = 2.125 ∧
    1 + 1 < england.L / england.aLC ∧ 1 + 1 < portugal.L / portugal.aLW := by sorry

end ComparativeAdvantage
